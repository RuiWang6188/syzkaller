// Copyright 2026 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package backend

import (
	"bufio"
	"bytes"
	"context"
	"encoding/json"
	"fmt"
	"io"
	"log"
	"math"
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

	// Shared-JSON mode: requests for sharedModel are admitted against sharedJSON, the flock'd
	// window an out-of-tree fleet already keeps, instead of this package's own per-model file.
	sharedJSON  string
	sharedModel string

	warnOnce sync.Once
}

var (
	limiterOnce sync.Once
	limiterInst *fileLimiter
)

func limiterFromEnv() *fileLimiter {
	tpm, _ := strconv.Atoi(os.Getenv("RECON_LLM_TPM"))
	rpm, _ := strconv.Atoi(os.Getenv("RECON_LLM_RPM"))
	sharedJSON := os.Getenv("RECON_LLM_SHARED_JSON")
	sharedModel := os.Getenv("RECON_LLM_SHARED_MODEL")
	if sharedJSON != "" && sharedModel == "" {
		sharedModel = defaultSharedModel
	}
	// Shared-JSON mode carries its own caps in the file, so it switches the limiter on by itself.
	if tpm <= 0 && rpm <= 0 && sharedJSON == "" {
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
	if sharedJSON != "" {
		log.Printf("llm limiter: model %v shares the budget in %v", sharedModel, sharedJSON)
	}
	return &fileLimiter{dir: dir, tpm: tpm, rpm: rpm, sharedJSON: sharedJSON, sharedModel: sharedModel}
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
	shared := l.sharedJSON != "" && model == l.sharedModel
	path := l.sharedJSON
	if !shared {
		path = filepath.Join(l.dir, sanitizeModel(model)+".window")
	}
	for {
		admit := l.tryAdmit
		if shared {
			admit = l.tryAdmitShared
		}
		wait, err := admit(path, tokens, time.Now())
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

// ---------------------------------------------------------------------------
// Shared-JSON mode.
//
// recon's dataflow arm runs beside the escaper arm -- a separate agent, in another language,
// in its own processes -- and both drive gemini-3.1-pro-preview. That is one account quota, so
// either they share one budget or neither arm's rate means anything. The escaper side already
// keeps a flock'd JSON window (escaper/agents/shared_ratelimit.py); rather than add a second
// limiter that cannot see the first, this reads and writes that same file. Its schema:
//
//	{"reqs": [unix_seconds, ...],
//	 "toks": [[unix_seconds, tokens, reservation_id], ...],
//	 "rpm_cap": int, "tpm_cap": int}
//
// The caps live in the file, not in the environment, so both fleets can be retuned by editing
// one field while they run. Keys this package does not know are preserved on write-back. The
// admission rule below is the Python one clause for clause -- including the empty-window escape,
// without which a single request larger than the whole cap waits forever -- so the two
// implementations cannot disagree about whether the window is full.
//
// Only the model named by RECON_LLM_SHARED_MODEL is admitted here. The flash helper tier has a
// separate quota and keeps its own per-model window file.
//
// One asymmetry, deliberate: the Python side reserves its estimate and then rewrites that entry
// with the response's actual total, while this side only ever writes the pre-send estimate --
// the response is not in scope at this call site. The estimate omits output and thinking
// tokens, so this arm under-reports by that much, and the cap is set with the headroom.

const defaultSharedModel = "gemini-3.1-pro-preview"

// sharedMaxSleep matches the Python side's `time.sleep(min(wait, 10))`: re-check the window at
// least every ten seconds rather than trusting one computed deadline, because the other fleet
// may free room sooner than the oldest entry's expiry implies.
const sharedMaxSleep = 10 * time.Second

func (l *fileLimiter) tryAdmitShared(path string, tokens int, now time.Time) (time.Duration, error) {
	f, err := os.OpenFile(path, os.O_RDWR|os.O_CREATE, 0o644)
	if err != nil {
		return 0, err
	}
	defer f.Close()
	if err := syscall.Flock(int(f.Fd()), syscall.LOCK_EX); err != nil {
		return 0, err
	}
	defer syscall.Flock(int(f.Fd()), syscall.LOCK_UN)

	doc := map[string]any{}
	if raw, err := io.ReadAll(f); err == nil && len(bytes.TrimSpace(raw)) > 0 {
		if err := json.Unmarshal(raw, &doc); err != nil {
			// A half-written file is not a reason to stall a fleet; start the window over.
			doc = map[string]any{}
		}
	}
	nowS := float64(now.UnixNano()) / 1e9
	rpm, tpm := l.rpm, l.tpm
	if v, ok := jsonNum(doc["rpm_cap"]); ok {
		rpm = int(v)
	}
	if v, ok := jsonNum(doc["tpm_cap"]); ok {
		tpm = int(v)
	}

	reqs, oldestReq := []any{}, 0.0
	for _, e := range jsonList(doc["reqs"]) {
		t, ok := jsonNum(e)
		if !ok || nowS-t >= limiterWindow.Seconds() {
			continue
		}
		if oldestReq == 0 || t < oldestReq {
			oldestReq = t
		}
		reqs = append(reqs, t)
	}
	toks, sumTok, oldestTok := []any{}, 0.0, 0.0
	for _, e := range jsonList(doc["toks"]) {
		row := jsonList(e)
		if len(row) < 2 {
			continue
		}
		t, ok := jsonNum(row[0])
		if !ok || nowS-t >= limiterWindow.Seconds() {
			continue
		}
		n, _ := jsonNum(row[1])
		sumTok += n
		if oldestTok == 0 || t < oldestTok {
			oldestTok = t
		}
		toks = append(toks, e)
	}

	wait := 0.0
	if rpm > 0 && len(reqs) >= rpm {
		wait = math.Max(wait, limiterWindow.Seconds()-(nowS-oldestReq)+0.05)
	}
	if tpm > 0 && len(toks) > 0 && sumTok+float64(tokens) > float64(tpm) {
		wait = math.Max(wait, limiterWindow.Seconds()-(nowS-oldestTok)+0.05)
	}
	if wait <= 0 {
		reqs = append(reqs, nowS)
		toks = append(toks, []any{nowS, tokens, reservationID()})
	}
	doc["reqs"] = reqs
	doc["toks"] = toks

	out, err := json.Marshal(doc)
	if err != nil {
		return 0, err
	}
	if err := f.Truncate(0); err != nil {
		return 0, err
	}
	if _, err := f.Seek(0, 0); err != nil {
		return 0, err
	}
	if _, err := f.Write(out); err != nil {
		return 0, err
	}
	// Durable and visible before the lock is dropped: the next process to take it must not read
	// the state this one replaced, or the reservation just made is lost and the cap is breached.
	if err := f.Sync(); err != nil {
		return 0, err
	}
	if wait <= 0 {
		return 0, nil
	}
	d := time.Duration(wait * float64(time.Second))
	if d > sharedMaxSleep {
		d = sharedMaxSleep
	}
	// A little jitter so two waiters do not wake into the same instant and race for one slot.
	return d + time.Duration(rand.Int63n(int64(500*time.Millisecond))), nil
}

func jsonNum(v any) (float64, bool) {
	f, ok := v.(float64)
	return f, ok
}

func jsonList(v any) []any {
	l, _ := v.([]any)
	return l
}

// reservationID is the Python side's uuid4().hex: the key it uses to rewrite an entry with the
// actual token count. Nothing here rewrites its own entries, but the field keeps the rows the
// two fleets write identical in shape.
func reservationID() string {
	return fmt.Sprintf("%016x%016x", rand.Uint64(), rand.Uint64())
}
