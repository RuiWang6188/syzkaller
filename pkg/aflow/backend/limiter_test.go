// Copyright 2026 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package backend

import (
	"context"
	"path/filepath"
	"testing"
	"time"
)

func TestLimiterAdmitsWithinWindow(t *testing.T) {
	l := &fileLimiter{dir: t.TempDir(), tpm: 1000, rpm: 3}
	path := filepath.Join(l.dir, "m.window")
	now := time.Now()
	for i, tok := range []int{300, 300, 300} {
		wait, err := l.tryAdmit(path, tok, now.Add(time.Duration(i)*time.Second))
		if err != nil || wait != 0 {
			t.Fatalf("request %d: wait=%v err=%v, want admission", i, wait, err)
		}
	}
	// Fourth request: the token window has room (900+50 <= 1000) but the request cap does not;
	// the wait ends when the first entry leaves the window, plus up to 2 s of jitter.
	wait, err := l.tryAdmit(path, 50, now.Add(3*time.Second))
	if err != nil || wait < 57*time.Second || wait > 59*time.Second+1 {
		t.Fatalf("over the request cap: wait=%v err=%v, want ~57s", wait, err)
	}
	// Tokens over the cap: two entries must expire (300+300+300+200 > 1000 -> drop two).
	wait, err = l.tryAdmit(path, 500, now.Add(3*time.Second))
	if err != nil || wait < 58*time.Second || wait > 60*time.Second+1 {
		t.Fatalf("over the token cap: wait=%v err=%v, want ~58s", wait, err)
	}
	// Once every entry has left the window (the last one was recorded at +2 s), everything is
	// admitted again.
	wait, err = l.tryAdmit(path, 900, now.Add(63*time.Second))
	if err != nil || wait != 0 {
		t.Fatalf("after the window: wait=%v err=%v, want admission", wait, err)
	}
}

func TestLimiterEmptyWindowAdmitsOversize(t *testing.T) {
	l := &fileLimiter{dir: t.TempDir(), tpm: 100}
	wait, err := l.tryAdmit(filepath.Join(l.dir, "m.window"), 10_000, time.Now())
	if err != nil || wait != 0 {
		t.Fatalf("oversize request into an empty window: wait=%v err=%v", wait, err)
	}
}

func TestLimitAcquireOffByDefault(t *testing.T) {
	t.Setenv("RECON_LLM_TPM", "")
	t.Setenv("RECON_LLM_RPM", "")
	limiterOnce.Do(func() { limiterInst = limiterFromEnv() })
	if limiterInst != nil {
		t.Skip("limiter configured by the environment of this test run")
	}
	if err := LimitAcquire(context.Background(), "m", 1<<30); err != nil {
		t.Fatalf("disabled limiter must admit: %v", err)
	}
}

func TestEstimateTokens(t *testing.T) {
	h := []*Message{{Role: RoleUser, Parts: []Part{{Text: "abcd"}}}}
	if got := EstimateTokens(h); got != (50+4)/4 {
		t.Fatalf("EstimateTokens = %d", got)
	}
}
