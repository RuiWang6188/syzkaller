// Copyright 2026 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package syzspec

import (
	"strings"
	"testing"

	"github.com/stretchr/testify/require"
)

func TestSeedBlobsEnabled_OffByDefault(t *testing.T) {
	require.False(t, SeedBlobsEnabled())
	t.Setenv("RECON_SEED_BLOBS", "1")
	require.True(t, SeedBlobsEnabled())
	t.Setenv("RECON_SEED_BLOBS", "0")
	require.False(t, SeedBlobsEnabled(), "only the exact string 1 enables it")
}

func TestUnresolvedBlobs(t *testing.T) {
	require.Empty(t, UnresolvedBlobs("mmap(&(0x7f0000000000), 0x1000)"))
	require.Empty(t, UnresolvedBlobs(`syz_mount_image$jfs(&AUTO='jfs\x00', &AUTO="abcd")`))
	// A well-formed placeholder that nothing registered.
	require.Equal(t, []string{`"$BLOB_a1b2c3d4e5f6"`},
		UnresolvedBlobs(`syz_mount_image$jfs(&AUTO='jfs\x00', &AUTO="$BLOB_a1b2c3d4e5f6")`))
	// Deduplicated, and only the exact 12-hex shape counts.
	got := UnresolvedBlobs(`"$BLOB_aaaaaaaaaaaa" "$BLOB_aaaaaaaaaaaa" "$BLOB_bbbbbbbbbbbb" "$BLOB_short"`)
	require.Equal(t, []string{`"$BLOB_aaaaaaaaaaaa"`, `"$BLOB_bbbbbbbbbbbb"`}, got)
}

// The failure this guards against: one wrong hex digit. The store round-trips the real token and
// leaves the mistyped one standing, so the detector is what separates them.
func TestUnresolvedBlobs_CatchesAMistypedDigit(t *testing.T) {
	var s BlobStore
	image := `"` + strings.Repeat("eJzs0000", 40) + `"`
	require.GreaterOrEqual(t, len(image), minBlobLen)
	ph := s.RegisterBlob(image)

	good := "syz_mount_image$jfs(&AUTO=" + ph + ")"
	require.Empty(t, UnresolvedBlobs(s.RestoreBlobs(good)))
	require.Contains(t, s.RestoreBlobs(good), "eJzs")

	// Flip the last hex digit of the token.
	bad := strings.Replace(good, ph[len(ph)-2:len(ph)-1], flip(ph[len(ph)-2:len(ph)-1]), 1)
	require.NotEqual(t, good, bad)
	restored := s.RestoreBlobs(bad)
	require.NotEmpty(t, UnresolvedBlobs(restored), "a mistyped token must be reported, not passed through")
	require.NotContains(t, restored, "eJzs", "and it must NOT have silently become an image")
}

func flip(hexDigit string) string {
	if hexDigit == "a" {
		return "b"
	}
	return "a"
}
