// Copyright 2026 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package crash

import (
	"errors"
	"fmt"
	"syscall"

	"github.com/google/syzkaller/pkg/aflow"
	"github.com/google/syzkaller/pkg/flatrpc"
	"github.com/google/syzkaller/pkg/fuzzer/queue"
	"github.com/google/syzkaller/pkg/hash"
	"github.com/google/syzkaller/pkg/log"
	"github.com/google/syzkaller/pkg/symbolizer"
	"github.com/google/syzkaller/prog"
	"github.com/google/syzkaller/sys/targets"
)

type ExecuteSeedArgs struct {
	TargetConfig
	ReproSyz string
	// recon: a kernel crash is the result to record, not a failure of the execution. The
	// execution is cached under its own kind ("recon-exec") so it never inherits a seed-exec
	// record whose BugTitle was the crash of an EARLIER program of that run (RecentCrashes
	// accumulates for the life of the RunnerManager), and only crashes that appear during
	// THIS submit are attributed to the program.
	CrashIsResult bool
	// Parse the program leniently. syzbot's reproducers are written against the syzkaller
	// descriptions of their day: a struct that has since grown a field makes the strict parse
	// reject the whole program ("missing struct fs_opt_elem[btrfs_options] fields 1/2"), even
	// though syz-execprog in the VM runs it fine. Only for programs that come from outside;
	// an agent's own program must stay strict, or it never learns that it wrote nonsense.
	Lenient bool
}

const deserializationErrorHelp = `

Syzlang Syntax Reminders:
- Multi-line statements are not supported. Each syscall must be on a single line.
- Inline comments (inside syscalls) are not supported. Put comments on their own lines.
- Double quotes ("...") are only for hex sequences. Use single quotes ('...') for strings and paths.`

// ExecuteSeedFunc boots the kernel and runs a single test program to collect coverage.
// It differs from ReproduceFuncWithCoverage in that it forces threaded mode and
// returns coverage data even if the execution fails with an error (e.g., timeout).
func ExecuteSeedFunc(ctx *aflow.Context, args ExecuteSeedArgs) (string, error) {
	if args.TargetArch == "" {
		args.TargetArch = targets.AMD64
	}

	target, err := prog.GetTarget(targets.Linux, args.TargetArch)
	if err != nil {
		return "", err
	}

	fullSyz := ctx.RestoreBlobs(args.ReproSyz)
	// We perform normalization so that the cache key is calculated correctly.
	mode := prog.Strict
	if args.Lenient {
		mode = prog.NonStrict
	}
	p, err := target.Deserialize([]byte(fullSyz), mode)
	if err != nil {
		return "", aflow.BadCallError("%v%s", ctx.ReplaceBlobs(err.Error()), deserializationErrorHelp)
	}
	if len(p.Calls) > prog.MaxCalls {
		return "", aflow.BadCallError("program has %d calls, exceeding the limit of %d", len(p.Calls), prog.MaxCalls)
	}
	fullSyz = string(p.Serialize())

	if args.Image == "" || len(args.VM) == 0 {
		return "", fmt.Errorf("VM configuration is missing")
	}
	imageHash, err := hash.File(args.Image)
	if err != nil {
		return "", err
	}

	kind := "seed-exec"
	if args.CrashIsResult {
		kind = "recon-exec"
	}
	desc := fmt.Sprintf("%s: kernel commit %v, kernel config hash %v, image hash %v,"+
		" vm %v, vm config hash %v, syz repro hash %v",
		kind, args.KernelCommit, hash.String(args.KernelConfig), imageHash.String(),
		args.Type, hash.String(args.VM), hash.String(fullSyz))
	cached, cachedID, err := aflow.CacheObject(ctx, kind, desc, func() (cachedExecution, error) {
		var res cachedExecution
		res.GeneratedSyz = args.ReproSyz

		rm, err := ctx.GetRunnerManager()
		if err != nil {
			return res, fmt.Errorf("failed to get runner manager: %w", err)
		}

		before := 0
		if args.CrashIsResult {
			before = len(rm.RecentCrashes())
		}
		runRes, err := rm.Submit(ctx.Context, p)
		if err != nil {
			if args.CrashIsResult {
				// the crash this program caused can tear down the submit itself; the
				// report is the result, not the transport error
				if crashes := rm.RecentCrashes(); len(crashes) > before {
					res.BugTitle = crashes[before].Title
					res.AltTitles = crashes[before].AltTitles
					res.Report = string(crashes[before].Report)
					return res, nil
				}
			}
			return res, aflow.FlowError(fmt.Errorf("RunnerManager Submit failed: %w", err))
		}

		log.Logf(1, "VM Console Output:\n%s", runRes.Output)

		crashes := rm.RecentCrashes()
		if args.CrashIsResult {
			crashes = crashes[before:]
			if len(crashes) > 0 {
				res.BugTitle = crashes[0].Title
				res.AltTitles = crashes[0].AltTitles
				res.Report = string(crashes[0].Report)
				for _, rep := range crashes[1:] {
					res.OtherReports = append(res.OtherReports, string(rep.Report))
				}
			}
		} else if len(crashes) > 0 {
			res.BugTitle = crashes[0].Title
			res.AltTitles = crashes[0].AltTitles
			res.Report = fmt.Sprintf("The kernel crashed after one of the previous executions:\n%s", string(crashes[0].Report))
			for _, rep := range crashes[1:] {
				res.OtherReports = append(res.OtherReports, string(rep.Report))
			}
		}

		if runRes.Status == queue.ExecFailure && runRes.Err != nil {
			res.Error = runRes.Err.Error()
		}

		if runRes.Info != nil {
			res.CallErrors = extractCallErrors(runRes.Info, p.Calls)
			var err error
			res.Coverage, err = extractCoverage(runRes.Info, args.TargetConfig)
			if err != nil {
				return res, err
			}
		}

		return res, nil
	})

	if err != nil {
		return "", err
	}
	if cached.Error != "" {
		return "", errors.New(cached.Error)
	}
	if cached.BugTitle != "" && !args.CrashIsResult {
		return "", fmt.Errorf("kernel crashed: %s", cached.BugTitle)
	}

	return cachedID, nil
}

// LoadCrash returns the crash a cached execution recorded and its report. With recon-exec
// semantics (ExecuteSeedArgs.CrashIsResult) that is the crash this program triggered; an
// empty title means it ran without crashing.
// LoadCrash returns the crash's identity under syzkaller's rule (titles.go) and its report.
func LoadCrash(ctx *aflow.Context, cachedID string) (TitleSet, string, error) {
	cached, err := aflow.RetrieveObject[cachedExecution](ctx, cachedID)
	if err != nil {
		return TitleSet{}, "", err
	}
	return TitleSet{Title: cached.BugTitle, AltTitles: cached.AltTitles}, cached.Report, nil
}

func extractCallErrors(info *flatrpc.ProgInfo, calls []*prog.Call) []CallError {
	var callErrors []CallError
	for i, call := range info.Calls {
		if call == nil {
			continue
		}
		if call.Error != 0 || call.Flags&flatrpc.CallFlagFinished == 0 {
			callName := "unknown"
			if i < len(calls) {
				callName = calls[i].Meta.Name
			}
			var errStr string
			if call.Flags&flatrpc.CallFlagExecuted == 0 {
				errStr = "call unexecuted (executor halted on an earlier call)"
			} else if call.Flags&flatrpc.CallFlagFinished == 0 {
				errStr = "call execution timed out or hung"
			} else {
				errStr = syscall.Errno(call.Error).Error()
			}
			callErrors = append(callErrors, CallError{
				Index:    i,
				CallName: callName,
				Errno:    call.Error,
				Error:    errStr,
			})
		}
	}
	return callErrors
}

// extractCoverage converts raw coverage PCs from ProgInfo into symbolized source code frames.
// It skips symbolization and returns nil if no coverage data was collected.
func extractCoverage(info *flatrpc.ProgInfo, args TargetConfig) ([][]symbolizer.Frame, error) {
	var cov [][]uint64
	hasCov := false
	for _, call := range info.Calls {
		if call == nil {
			cov = append(cov, nil)
			continue
		}
		cov = append(cov, call.Cover)
		if len(call.Cover) > 0 {
			hasCov = true
		}
	}
	if info.Extra != nil && len(info.Extra.Cover) > 0 {
		cov = append(cov, info.Extra.Cover)
		hasCov = true
	} else {
		cov = append(cov, nil)
	}
	if !hasCov {
		return nil, nil
	}
	symbolized, err := symbolize(args, cov)
	if err != nil {
		return nil, fmt.Errorf("failed to symbolize coverage: %w", err)
	}
	return symbolized, nil
}
