// Copyright 2026 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package backend

import (
	"encoding/json"
	"os"
	"path/filepath"
	"testing"
	"time"
)

// The shared-JSON window is written by another fleet, in another language. These tests pin the
// schema and the admission rule, because a disagreement about either is invisible at runtime:
// both sides would keep admitting and the account quota, not the limiter, would say no.

func readDoc(t *testing.T, path string) map[string]any {
	t.Helper()
	raw, err := os.ReadFile(path)
	if err != nil {
		t.Fatal(err)
	}
	doc := map[string]any{}
	if err := json.Unmarshal(raw, &doc); err != nil {
		t.Fatalf("state file is not the JSON the other fleet reads: %v", err)
	}
	return doc
}

func TestSharedAdmitsAndWritesThePythonSchema(t *testing.T) {
	path := filepath.Join(t.TempDir(), "escaper.json")
	if err := os.WriteFile(path, []byte(`{"reqs": [], "toks": [], "rpm_cap": 20, "tpm_cap": 700000}`), 0o644); err != nil {
		t.Fatal(err)
	}
	l := &fileLimiter{sharedJSON: path, sharedModel: "m"}
	wait, err := l.tryAdmitShared(path, 1000, time.Now())
	if err != nil || wait != 0 {
		t.Fatalf("empty window must admit at once: wait=%v err=%v", wait, err)
	}
	doc := readDoc(t, path)
	reqs, _ := doc["reqs"].([]any)
	toks, _ := doc["toks"].([]any)
	if len(reqs) != 1 || len(toks) != 1 {
		t.Fatalf("one admitted request must leave one entry in each list: %v", doc)
	}
	row, _ := toks[0].([]any)
	if len(row) != 3 {
		t.Fatalf("a token row is [unix_seconds, tokens, reservation_id]: %v", row)
	}
	if n, _ := row[1].(float64); n != 1000 {
		t.Fatalf("the row must carry the estimate it reserved: %v", row)
	}
	if id, ok := row[2].(string); !ok || len(id) != 32 {
		t.Fatalf("reservation id must be the 32-hex the Python side writes: %v", row[2])
	}
	// The caps are the other fleet's tuning knob; losing them on write-back would silently
	// fall the whole window back to this process's environment.
	if c, _ := doc["tpm_cap"].(float64); c != 700000 {
		t.Fatalf("tpm_cap must survive write-back: %v", doc["tpm_cap"])
	}
}

func TestSharedHoldsWhenTheWindowIsFull(t *testing.T) {
	path := filepath.Join(t.TempDir(), "escaper.json")
	now := time.Now()
	nowS := float64(now.UnixNano()) / 1e9
	doc := map[string]any{
		"reqs":    []any{nowS - 5},
		"toks":    []any{[]any{nowS - 5, 690000, "abc"}},
		"rpm_cap": 20, "tpm_cap": 700000,
	}
	raw, _ := json.Marshal(doc)
	if err := os.WriteFile(path, raw, 0o644); err != nil {
		t.Fatal(err)
	}
	l := &fileLimiter{sharedJSON: path, sharedModel: "m"}
	wait, err := l.tryAdmitShared(path, 50000, now)
	if err != nil {
		t.Fatal(err)
	}
	// 690k + 50k is over the 700k cap, so the request waits for the 5-second-old entry to age
	// out of the minute: ~55 s, clamped to the ten-second re-check.
	if wait <= 0 || wait > sharedMaxSleep+time.Second {
		t.Fatalf("a full window must hold the request and re-check within %v: got %v", sharedMaxSleep, wait)
	}
	if n := len(jsonList(readDoc(t, path)["toks"])); n != 1 {
		t.Fatalf("a held request must not reserve anything: %v rows", n)
	}
}

func TestSharedAdmitsARequestBiggerThanTheWholeCap(t *testing.T) {
	// The Python side's `s["toks"] and` guard: on an empty window a request larger than the cap
	// is admitted, because no amount of waiting could ever make it fit.
	path := filepath.Join(t.TempDir(), "escaper.json")
	if err := os.WriteFile(path, []byte(`{"reqs": [], "toks": [], "tpm_cap": 1000}`), 0o644); err != nil {
		t.Fatal(err)
	}
	l := &fileLimiter{sharedJSON: path, sharedModel: "m"}
	wait, err := l.tryAdmitShared(path, 999999, time.Now())
	if err != nil || wait != 0 {
		t.Fatalf("an oversized request on an empty window must go out: wait=%v err=%v", wait, err)
	}
}

func TestSharedPrunesTheTrailingMinuteAndKeepsUnknownKeys(t *testing.T) {
	path := filepath.Join(t.TempDir(), "escaper.json")
	now := time.Now()
	nowS := float64(now.UnixNano()) / 1e9
	doc := map[string]any{
		"reqs":     []any{nowS - 120, nowS - 5},
		"toks":     []any{[]any{nowS - 120, 500000, "old"}, []any{nowS - 5, 10, "new"}},
		"tpm_cap":  700000,
		"some_key": "a field this package does not know about",
	}
	raw, _ := json.Marshal(doc)
	if err := os.WriteFile(path, raw, 0o644); err != nil {
		t.Fatal(err)
	}
	l := &fileLimiter{sharedJSON: path, sharedModel: "m"}
	if wait, err := l.tryAdmitShared(path, 10, now); err != nil || wait != 0 {
		t.Fatalf("the two-minute-old entries must not count: wait=%v err=%v", wait, err)
	}
	got := readDoc(t, path)
	if n := len(jsonList(got["reqs"])); n != 2 { // the 5s-old one plus ours
		t.Fatalf("expired requests must be dropped, fresh ones kept: %v rows", n)
	}
	if got["some_key"] != "a field this package does not know about" {
		t.Fatalf("unknown keys must survive write-back: %v", got)
	}
}

func TestSharedOnlyClaimsItsOwnModel(t *testing.T) {
	// The helper tier is a different model with a different quota; sending it to the shared
	// window would make the two fleets throttle each other over a budget they do not share.
	dir := t.TempDir()
	path := filepath.Join(dir, "escaper.json")
	if err := os.WriteFile(path, []byte(`{"reqs": [], "toks": [], "tpm_cap": 700000}`), 0o644); err != nil {
		t.Fatal(err)
	}
	l := &fileLimiter{dir: dir, sharedJSON: path, sharedModel: "gemini-3.1-pro-preview"}
	if err := l.acquire(t.Context(), "gemini-3.7-flash", 10); err != nil {
		t.Fatal(err)
	}
	if n := len(jsonList(readDoc(t, path)["toks"])); n != 0 {
		t.Fatalf("a flash call must not land in the pro window: %v rows", n)
	}
	if err := l.acquire(t.Context(), "gemini-3.1-pro-preview", 10); err != nil {
		t.Fatal(err)
	}
	if n := len(jsonList(readDoc(t, path)["toks"])); n != 1 {
		t.Fatalf("the shared model must land in the shared window: %v rows", n)
	}
}
