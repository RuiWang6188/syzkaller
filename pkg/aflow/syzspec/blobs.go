// Copyright 2026 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

// Package syzspec provides utilities and actions for parsing and analyzing syzlang descriptions.
package syzspec

import (
	"crypto/sha256"
	"encoding/hex"
	"fmt"
	"os"
	"regexp"
	"sync"
)

const minBlobLen = 128

var (
	StringLiteralSeq = regexp.MustCompile(`"(?:[^"\\]|\\.)*"(?:\s*"(?:[^"\\]|\\.)*")*`)
	placeholderRegex = regexp.MustCompile(`"\$BLOB_[a-f0-9]{12}"`)
)

// SeedBlobsEnabled reports whether a long string literal in tool output should be registered as a
// placeholder instead of being horizontally truncated, and whether an unresolved placeholder
// reaching execution should be reported rather than passed through.
//
// OFF unless RECON_SEED_BLOBS=1. It gates a capability change -- an agent that can read a
// filesystem image out of a test seed can reproduce bugs it otherwise cannot -- and a benchmark
// scored half under each regime cannot be compared. With it off every affected path is the
// identity, so a running campaign is unaffected.
func SeedBlobsEnabled() bool {
	return os.Getenv("RECON_SEED_BLOBS") == "1"
}

// UnresolvedBlobs returns the placeholders in content that RestoreBlobs left standing.
//
// RestoreBlobs returns an unknown placeholder unchanged, which is the right thing for text that
// merely mentions one but the wrong thing for a program about to execute: a single mistyped hex
// digit turns a 32KB filesystem image into the 20-byte literal "$BLOB_a1b2c3d4e5f6", the mount
// fails, and nothing says why. Copying a 12-hex token by hand is exactly the kind of thing a
// model gets wrong occasionally, so the caller can turn a silent wrong answer into a correctable
// error.
func UnresolvedBlobs(content string) []string {
	var out []string
	seen := map[string]bool{}
	for _, m := range placeholderRegex.FindAllString(content, -1) {
		if !seen[m] {
			seen[m] = true
			out = append(out, m)
		}
	}
	return out
}

// BlobStore manages the mapping between large data blobs and their placeholders.
type BlobStore struct {
	mu                sync.RWMutex
	placeholderToBlob map[string]string
}

// RegisterBlob registers a data blob string and returns its placeholder.
func (s *BlobStore) RegisterBlob(blob string) string {
	h := sha256.Sum256([]byte(blob))
	hashStr := hex.EncodeToString(h[:6]) // Use 12 hex characters.
	ph := fmt.Sprintf("\"$BLOB_%s\"", hashStr)

	s.mu.Lock()
	defer s.mu.Unlock()
	if s.placeholderToBlob == nil {
		s.placeholderToBlob = make(map[string]string)
	}
	s.placeholderToBlob[ph] = blob
	return ph
}

// ReplaceBlobs replaces all large string literal blobs in the content with their placeholders.
func (s *BlobStore) ReplaceBlobs(content string) string {
	return StringLiteralSeq.ReplaceAllStringFunc(content, func(match string) string {
		if len(match) >= minBlobLen {
			return s.RegisterBlob(match)
		}
		return match
	})
}

// RestoreBlobs restores all placeholders in the content back to their original blobs.
func (s *BlobStore) RestoreBlobs(content string) string {
	s.mu.RLock()
	defer s.mu.RUnlock()
	if len(s.placeholderToBlob) == 0 {
		return content
	}
	return placeholderRegex.ReplaceAllStringFunc(content, func(match string) string {
		if blob, ok := s.placeholderToBlob[match]; ok {
			return blob
		}
		return match
	})
}
