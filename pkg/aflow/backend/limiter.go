// Copyright 2026 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package backend

import (
	"bufio"
	"context"
	"fmt"
	"log"
	"math/rand"
	"os"
	"path/filepath"
	"strconv"
	"strings"
	"sync"
	"syscall"
	"time"
)

// A cross-process sliding-window limiter for one API key, keyed by model.
//
// recon runs a dozen independent processes against one Gemini key. Measured on 2026-09-15
// (results/token-usage, results/api-concurrency): the 429s track the SUM of prompt tokens all
// those processes send per minute per model, not the size of any one request; 43% of them land
// within two seconds of another process's 429, because every rejected request slept a flat
// minute and woke up together; and each 429 cost that minute plus, after two, a switch to a
// weaker model. Waiting for the provider to say no is the expensive way to queue. This queues
// locally instead: a process asks for admission before each real request, and sleeps only until
// the window has room. Off unless RECON_LLM_TPM or RECON_LLM_RPM is set, so nothing changes for
// a binary that is not launched with them.
//
// State is a small text file per model under RECON_LLM_LIMIT_DIR (default $TMPDIR/recon-llm-
// limiter), one "unixnano tokens" line per admitted request in the last minute, guarded by
// flock so every process on the box sees the same window. Tokens are an estimate made before
// the request (EstimateTokens); set the limit with that margin in mind. A limiter failure
// (unwritable directory, a corrupt file) never fails a request: it is logged once and admission
// is granted.

const limiterWindow = time.Minute

type fileLimiter struct {
	dir string
	tpm int // prompt tokens per minute per model; 0 = unlimited
	rpm int // requests per minute per model; 0 = unlimited

	warnOnce sync.Once
}

var (
	limiterOnce sync.Once
	limiterInst *fileLimiter
)

func limiterFromEnv() *fileLimiter {
	tpm, _ := strconv.Atoi(os.Getenv("RECON_LLM_TPM"))
	rpm, _ := strconv.Atoi(os.Getenv("RECON_LLM_RPM"))
	if tpm <= 0 && rpm <= 0 {
		return nil
	}
	dir := os.Getenv("RECON_LLM_LIMIT_DIR")
	if dir == "" {
		dir = filepath.Join(os.TempDir(), "recon-llm-limiter")
	}
	if err := os.MkdirAll(dir, 0o755); err != nil {
		log.Printf("llm limiter: cannot create %v: %v; limiter disabled", dir, err)
		return nil
	}
	log.Printf("llm limiter: %v tokens/min, %v requests/min per model, window state in %v", tpm, rpm, dir)
	return &fileLimiter{dir: dir, tpm: tpm, rpm: rpm}
}

// LimitAcquire blocks until the shared per-minute window for model has room for a request of
// the given (estimated) size, then records it. It returns only ctx's error.
func LimitAcquire(ctx context.Context, model string, tokens int) error {
	limiterOnce.Do(func() { limiterInst = limiterFromEnv() })
	l := limiterInst
	if l == nil {
		return nil
	}
	return l.acquire(ctx, model, tokens)
}

func (l *fileLimiter) acquire(ctx context.Context, model string, tokens int) error {
	path := filepath.Join(l.dir, sanitizeModel(model)+".window")
	for {
		wait, err := l.tryAdmit(path, tokens, time.Now())
		if err != nil {
			l.warnOnce.Do(func() { log.Printf("llm limiter: %v; admitting without limit", err) })
			return nil
		}
		if wait <= 0 {
			return nil
		}
		select {
		case <-ctx.Done():
			return ctx.Err()
		case <-time.After(wait):
		}
	}
}

type windowEntry struct {
	at     time.Time
	tokens int
}

// tryAdmit records the request and returns 0 when the window has room, or the time to sleep
// before asking again (the moment the oldest entries that must expire to make room do expire,
// plus a little jitter so the waiters of one key do not return in lockstep).
func (l *fileLimiter) tryAdmit(path string, tokens int, now time.Time) (time.Duration, error) {
	f, err := os.OpenFile(path, os.O_RDWR|os.O_CREATE, 0o644)
	if err != nil {
		return 0, err
	}
	defer f.Close()
	if err := syscall.Flock(int(f.Fd()), syscall.LOCK_EX); err != nil {
		return 0, err
	}
	defer syscall.Flock(int(f.Fd()), syscall.LOCK_UN)

	var entries []windowEntry
	sc := bufio.NewScanner(f)
	for sc.Scan() {
		fields := strings.Fields(sc.Text())
		if len(fields) != 2 {
			continue
		}
		ns, err1 := strconv.ParseInt(fields[0], 10, 64)
		tok, err2 := strconv.Atoi(fields[1])
		if err1 != nil || err2 != nil {
			continue
		}
		at := time.Unix(0, ns)
		if now.Sub(at) < limiterWindow {
			entries = append(entries, windowEntry{at: at, tokens: tok})
		}
	}
	sumTokens := 0
	for _, e := range entries {
		sumTokens += e.tokens
	}
	fits := func(sumTok, n int) bool {
		return (l.tpm <= 0 || sumTok+tokens <= l.tpm) && (l.rpm <= 0 || n+1 <= l.rpm)
	}
	var wait time.Duration
	if fits(sumTokens, len(entries)) || len(entries) == 0 {
		// An empty window always admits: a request larger than the whole limit must still go
		// out, or it would wait forever.
		entries = append(entries, windowEntry{at: now, tokens: tokens})
	} else {
		// Expire the oldest entries until the request fits; the wait ends when the last of
		// those leaves the window.
		sumTok, n := sumTokens, len(entries)
		for _, e := range entries {
			sumTok -= e.tokens
			n--
			if fits(sumTok, n) {
				wait = e.at.Add(limiterWindow).Sub(now)
				break
			}
		}
		if wait <= 0 {
			wait = time.Second
		}
		wait += time.Duration(rand.Int63n(int64(2 * time.Second)))
	}
	if err := f.Truncate(0); err != nil {
		return 0, err
	}
	if _, err := f.Seek(0, 0); err != nil {
		return 0, err
	}
	w := bufio.NewWriter(f)
	for _, e := range entries {
		fmt.Fprintf(w, "%d %d\n", e.at.UnixNano(), e.tokens)
	}
	if err := w.Flush(); err != nil {
		return 0, err
	}
	return wait, nil
}

func sanitizeModel(model string) string {
	return strings.Map(func(r rune) rune {
		if r >= 'a' && r <= 'z' || r >= 'A' && r <= 'Z' || r >= '0' && r <= '9' || r == '-' || r == '.' || r == '_' {
			return r
		}
		return '_'
	}, model)
}

// EstimateTokens is the prompt size a request will be charged, before it is sent: text and tool
// payload bytes at four per token, plus a small per-message overhead. It is an estimate; the
// exact count only exists in the response.
func EstimateTokens(history []*Message) int {
	bytes := 0
	for _, m := range history {
		bytes += 50
		for _, p := range m.Parts {
			bytes += len(p.Text)
			if p.FunctionCall != nil {
				bytes += len(fmt.Sprint(p.FunctionCall.Args)) + len(p.FunctionCall.Name)
			}
			if p.FunctionResponse != nil {
				bytes += len(fmt.Sprint(p.FunctionResponse.Response)) + len(p.FunctionResponse.Name)
			}
		}
	}
	return bytes / 4
}
