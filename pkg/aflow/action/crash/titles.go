// Copyright 2025 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package crash

import (
	"encoding/json"
	"errors"
	"regexp"
	"slices"
	"strings"

	"github.com/google/syzkaller/pkg/aflow"
	"github.com/google/syzkaller/pkg/log"
	"github.com/google/syzkaller/pkg/mgrconfig"
	"github.com/google/syzkaller/pkg/report"
)

// Deciding whether two crashes are the same bug.
//
// A crash report carries no title: pkg/report derives one from the text, together with a set of
// alternative titles built from the format's own alt templates and from the guilty frame with
// known prefixes stripped (report.go:496-553). The rule that uses them is stated in the tree:
//
//	// If two crashes have a non-empty intersection of Title/AltTitles, they are considered
//	// the same bug.
//	                                                             -- pkg/report/report.go:47
//
// That is what syzbot itself does: syz-manager sends the whole set (manager.go:744), and
// findBugForCrash matches an incoming crash against a bug's accumulated set rather than against
// its display title (dashboard/app/api.go:874, :1440-1498, :947).
//
// Comparing display titles instead is wrong in a way that matters here, because a bug's display
// title is frozen at creation while its crashes keep moving: of one bug's 93 recorded crashes
// only 5 carry the wording the dashboard shows. A title changes for the same defect when a
// sanitizer is reworded between versions, when a different sanitizer fires first on the same
// access, when inlining moves the guilty frame, or when syzkaller's own frame skip-list changes.

// syzbot's dashboard appends a duplicate-signature counter to a bug's display title ("... (3)").
// A kernel crash report never carries one, so it is stripped before comparing. Crash-side titles
// are unaffected; only a title taken from the dashboard can have it.
var dashboardCounter = regexp.MustCompile(`\s*\(\d+\)$`)

// Both narrow the expected set to the declared title alone, which silently turns the rule back
// into a string comparison. They are errors so that the one caller logs them; neither is fatal.
var (
	errNoReport       = errors.New("no crash report to derive alternative titles from")
	errUnparsedReport = errors.New("the bug's own crash report did not parse")
)

// NormalizeTitle prepares a title for comparison. Deliberately minimal: anything beyond
// trimming and dropping the dashboard counter would be a similarity heuristic of our own, and
// the whole point of this file is to not have one.
func NormalizeTitle(title string) string {
	return dashboardCounter.ReplaceAllString(strings.TrimSpace(title), "")
}

// TitleSet is one crash's identity: the representative title plus the alternatives pkg/report
// derived for it. Two TitleSets name the same bug when they intersect.
type TitleSet struct {
	Title     string   `json:",omitempty"`
	AltTitles []string `json:",omitempty"`
}

// TitleSetOf collects the set pkg/report derived for a parsed crash.
func TitleSetOf(rep *report.Report) TitleSet {
	if rep == nil {
		return TitleSet{}
	}
	return TitleSet{Title: rep.Title, AltTitles: slices.Clone(rep.AltTitles)}
}

// All returns the normalized, deduplicated titles, representative first.
func (s TitleSet) All() []string {
	var out []string
	for _, t := range append([]string{s.Title}, s.AltTitles...) {
		if t = NormalizeTitle(t); t != "" && !slices.Contains(out, t) {
			out = append(out, t)
		}
	}
	return out
}

func (s TitleSet) Empty() bool { return len(s.All()) == 0 }

// SameBug is syzkaller's own rule: a non-empty intersection of the two title sets. An empty set
// on either side is not a match -- "we could not parse a title" must never read as "same bug".
func SameBug(a, b TitleSet) bool {
	other := b.All()
	for _, t := range a.All() {
		if slices.Contains(other, t) {
			return true
		}
	}
	return false
}

// ExpectedTitles derives the title set of the bug under test from the crash report that defines
// it -- syzbot's published report for the target bug. Parsing it with the same reporter that
// parses our own crashes is what makes the two sides comparable: a reporter built without
// KernelObj cannot strip source paths or collapse inlined frames, and produces titles that name
// a different frame, so both sides must come from the configured reporter or neither.
//
// Falls back to the bare title when there is no report to parse (the gate's inputs historically
// carried only a title), so a caller always gets a usable set.
func ExpectedTitles(args TargetConfig, workdir, bugTitle, crashReport string) (TitleSet, error) {
	bare := TitleSet{Title: bugTitle}
	if strings.TrimSpace(crashReport) == "" {
		return bare, errNoReport
	}
	cfg, err := BuildConfig(args, workdir)
	if err != nil {
		return bare, err
	}
	set, err := parseTitles(cfg, crashReport)
	if err != nil {
		return bare, err
	}
	if set.Empty() {
		return bare, errUnparsedReport
	}
	// Keep the declared title in the set as well: it is the name the bug is known by, and the
	// report we were given may be one crash of several the bug has produced.
	if NormalizeTitle(bugTitle) != "" && !slices.Contains(set.All(), NormalizeTitle(bugTitle)) {
		set.AltTitles = append(set.AltTitles, bugTitle)
	}
	return set, nil
}

func parseTitles(cfg *mgrconfig.Config, text string) (TitleSet, error) {
	reporter, err := report.NewReporter(cfg)
	if err != nil {
		return TitleSet{}, err
	}
	return TitleSetOf(reporter.Parse([]byte(text))), nil
}

// BugTitlesArgs derives the identity of the bug under test once per flow, so that every
// comparison in that flow uses the same set rather than re-deriving one.
// Fields are listed rather than embedding TargetConfig: embedding would demand StraceBin,
// NeedStrace, Sandbox and Snapshot from every flow that uses this action, and none of them
// affects how a report is parsed.
type BugTitlesArgs struct {
	AgentName    string
	TargetArch   string
	Syzkaller    string
	Image        string
	Type         string
	VM           json.RawMessage
	KernelSrc    string
	KernelObj    string
	KernelCommit string
	KernelConfig string
	BugTitle     string
	CrashReport  string
	// Titles syzbot itself recorded under this bug id. The same notion as AltTitles, taken from
	// the accumulation the dashboard actually performed -- it merges every accepted crash's set
	// into the bug (dashboard/app/api.go:947) -- instead of re-derived from one report. It
	// matters because re-deriving often yields nothing: 261 of 368 of this corpus's syzbot
	// reports produce no alternative at all. Plain "WARNING in f" has no alt template, and a
	// KASAN report whose first BUG line names an inlined frame parses corrupted (51 of 368, 42
	// of them KASAN). Without this the expected side stays the bare declared title for most of
	// the benchmark, which is the comparison the rule replaces.
	BugKnownTitles []string
}

func (a BugTitlesArgs) targetConfig() TargetConfig {
	return TargetConfig{
		AgentName:    a.AgentName,
		TargetArch:   a.TargetArch,
		Syzkaller:    a.Syzkaller,
		Image:        a.Image,
		Type:         a.Type,
		VM:           a.VM,
		KernelSrc:    a.KernelSrc,
		KernelObj:    a.KernelObj,
		KernelCommit: a.KernelCommit,
		KernelConfig: a.KernelConfig,
	}
}

type BugTitlesResult struct {
	// Alternative titles of the bug under test. With BugTitle they form the expected side of
	// every same-bug comparison in the flow.
	BugAltTitles []string
}

// ActionBugTitles parses the target bug's own crash report with the configured reporter and
// records the alternative titles it derives. Placed after the kernel build, because a reporter
// without KernelObj cannot strip source paths or collapse inlined frames and would derive a set
// that names a different frame than the one our own crashes are parsed into.
var ActionBugTitles = aflow.NewFuncAction("bug-titles",
	func(ctx *aflow.Context, args BugTitlesArgs) (BugTitlesResult, error) {
		workdir, err := ctx.TempDir()
		if err != nil {
			return BugTitlesResult{}, err
		}
		set, err := ExpectedTitles(args.targetConfig(), workdir, args.BugTitle, args.CrashReport)
		if err != nil {
			// A bug whose report yields nothing still has its declared title and whatever syzbot
			// recorded. Narrower, but the flow runs.
			log.Logf(0, "bug-titles: no alternatives from the report (%v)", err)
			set = TitleSet{Title: args.BugTitle}
		}
		set.AltTitles = append(set.AltTitles, args.BugKnownTitles...)
		// All(), not AltTitles: ExpectedSet reinstalls the declared title as the representative,
		// so the title the reporter actually derived would otherwise be dropped. For a format
		// with no alt templates -- plain "WARNING in f" has none -- that left the expected side
		// as exactly {declared title}, which is the comparison this change exists to replace.
		return BugTitlesResult{BugAltTitles: set.All()}, nil
	})

// ExpectedSet rebuilds the expected side from the two flow variables ActionBugTitles produces.
// Every comparison should go through this so there is exactly one notion of the bug's identity.
func ExpectedSet(bugTitle string, bugAltTitles []string) TitleSet {
	return TitleSet{Title: bugTitle, AltTitles: bugAltTitles}
}

// ActionIgnoreAltTitles absorbs the alternative titles in a flow that does not judge bug
// identity. aflow requires every action output to be consumed by something downstream
// (verify.go:80), and the patching flows reproduce a crash only to describe it to an agent --
// they never ask whether two crashes are the same bug, so there is nothing there to convert.
// An explicit sink says that, where a stray unused field in some other action's arguments
// would not.
var ActionIgnoreAltTitles = aflow.NewFuncAction("ignore-alt-titles",
	func(_ *aflow.Context, _ struct {
		ReproducedAltTitles []string
	}) (struct{}, error) {
		return struct{}{}, nil
	})
