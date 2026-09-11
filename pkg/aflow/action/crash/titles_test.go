// Copyright 2025 syzkaller project authors. All rights reserved.
// Use of this source code is governed by Apache 2 LICENSE that can be found in the LICENSE file.

package crash

import (
	"reflect"
	"testing"
)

func TestNormalizeTitle(t *testing.T) {
	for _, test := range []struct{ in, want string }{
		{"WARNING in __kvm_gpc_refresh (3)", "WARNING in __kvm_gpc_refresh"},
		{"  WARNING in foo  ", "WARNING in foo"},
		{"KASAN: use-after-free Read in f (12)", "KASAN: use-after-free Read in f"},
		// Not a dashboard counter: a parenthesised number inside the title stays.
		{"BUG: corrupted list in (4) frames", "BUG: corrupted list in (4) frames"},
		{"", ""},
	} {
		if got := NormalizeTitle(test.in); got != test.want {
			t.Errorf("NormalizeTitle(%q) = %q, want %q", test.in, got, test.want)
		}
	}
}

func TestTitleSetAll(t *testing.T) {
	s := TitleSet{
		Title:     "KASAN: slab-use-after-free Read in v4l2_fh_open (2)",
		AltTitles: []string{"bad-access in v4l2_fh_open", "", "KASAN: slab-use-after-free Read in v4l2_fh_open"},
	}
	want := []string{"KASAN: slab-use-after-free Read in v4l2_fh_open", "bad-access in v4l2_fh_open"}
	if got := s.All(); !reflect.DeepEqual(got, want) {
		t.Errorf("All() = %q, want %q", got, want)
	}
	if (TitleSet{}).Empty() != true {
		t.Error("the empty set should report Empty")
	}
	if (TitleSet{AltTitles: []string{"  "}}).Empty() != true {
		t.Error("a set of only blanks should report Empty")
	}
}

func TestSameBug(t *testing.T) {
	for _, test := range []struct {
		name     string
		a, b     TitleSet
		wantSame bool
	}{{
		// The dashboard title is frozen at filing; the kernel's KASAN wording changed under it.
		// Of this bug's 93 recorded crashes, 5 carry the first spelling and 88 the second.
		name:     "sanitizer reworded between kernel versions",
		a:        TitleSet{Title: "KASAN: use-after-free Read in v4l2_fh_open", AltTitles: []string{"bad-access in v4l2_fh_open"}},
		b:        TitleSet{Title: "KASAN: slab-use-after-free Read in v4l2_fh_open", AltTitles: []string{"bad-access in v4l2_fh_open"}},
		wantSame: true,
	}, {
		// UBSAN's index check fires before KASAN's shadow check on the same access. syzbot
		// merges the two because both formats emit the same bad-access alternative.
		name:     "a different sanitizer fires first",
		a:        TitleSet{Title: "KASAN: slab-use-after-free Write in dtSplitPage", AltTitles: []string{"bad-access in dtSplitPage"}},
		b:        TitleSet{Title: "UBSAN: array-index-out-of-bounds in dtSplitPage", AltTitles: []string{"bad-access in dtSplitPage"}},
		wantSame: true,
	}, {
		name:     "the representative titles happen to match",
		a:        TitleSet{Title: "WARNING in foo"},
		b:        TitleSet{Title: "WARNING in foo", AltTitles: []string{"WARNING in bar"}},
		wantSame: true,
	}, {
		// Same subsystem, same shape, different function: nothing in either set matches.
		name:     "different bug in a neighbouring function",
		a:        TitleSet{Title: "KASAN: slab-use-after-free Read in roccat_open", AltTitles: []string{"bad-access in roccat_open"}},
		b:        TitleSet{Title: "KASAN: slab-use-after-free Read in roccat_disconnect", AltTitles: []string{"bad-access in roccat_disconnect"}},
		wantSame: false,
	}, {
		// A WARNING and a fault in the same function do NOT merge: the generic WARNING format
		// has no alternative title, which is precisely why "same crashing function" is not the
		// rule -- it would accept this pair and syzkaller does not.
		name:     "warning and fault in the same function",
		a:        TitleSet{Title: "general protection fault in bfs_get_block", AltTitles: []string{"bad-access in bfs_get_block"}},
		b:        TitleSet{Title: "WARNING in bfs_get_block"},
		wantSame: false,
	}, {
		name:     "an unparsed crash is never the same bug",
		a:        TitleSet{Title: "KASAN: slab-use-after-free Read in foo"},
		b:        TitleSet{},
		wantSame: false,
	}, {
		name:     "two unparsed crashes are not the same bug either",
		a:        TitleSet{},
		b:        TitleSet{},
		wantSame: false,
	}, {
		name:     "the dashboard counter does not prevent a match",
		a:        TitleSet{Title: "WARNING in __kvm_gpc_refresh (3)"},
		b:        TitleSet{Title: "WARNING in __kvm_gpc_refresh"},
		wantSame: true,
	}} {
		t.Run(test.name, func(t *testing.T) {
			if got := SameBug(test.a, test.b); got != test.wantSame {
				t.Errorf("SameBug = %v, want %v", got, test.wantSame)
			}
			if got := SameBug(test.b, test.a); got != test.wantSame {
				t.Errorf("SameBug is not symmetric: reversed = %v, want %v", got, test.wantSame)
			}
		})
	}
}

func TestExpectedSetKeepsDeclaredTitle(t *testing.T) {
	set := ExpectedSet("WARNING in foo (2)", []string{"bad-access in foo"})
	if !SameBug(set, TitleSet{Title: "WARNING in foo"}) {
		t.Error("the declared title must stay part of the expected set")
	}
	if !SameBug(set, TitleSet{Title: "UBSAN: array-index-out-of-bounds in foo", AltTitles: []string{"bad-access in foo"}}) {
		t.Error("an alternative title must also match")
	}
}
