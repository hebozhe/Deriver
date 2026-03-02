package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
	"testing"
)

func ndTestParseWff(t *testing.T, s string) (wff *fmla.WffTree) {
	var ok bool

	t.Helper()

	if wff, ok = fmla.ParseStringToWff(s); !ok {
		t.Fatalf("Failed to parse %q.", s)
	}

	return
}

func ndTestParseWffs(t *testing.T, ss ...string) (wffs []*fmla.WffTree) {
	var (
		s   string
		wff *fmla.WffTree
		ok  bool
	)

	t.Helper()

	for _, s = range ss {
		if wff, ok = fmla.ParseStringToWff(s); !ok {
			t.Fatalf("Failed to parse %q.", s)
		}

		wffs = append(wffs, wff)
	}

	return
}

type testCase struct {
	prems []string
	goal  string
	infS  pr.InfStrength
	modS  pr.ModStrength
}

var tcs []testCase = []testCase{
	// Implicational theorems, with premises:
	{[]string{"A"}, "A", pr.Implicational, pr.NoSystem},
	{[]string{"A"}, "B -> A", pr.Implicational, pr.NoSystem},
	{[]string{"A -> (A -> B)"}, "A -> B", pr.Implicational, pr.NoSystem},
	{[]string{"A -> (B -> C)"}, "B -> (A -> C)", pr.Implicational, pr.NoSystem},
	{[]string{"A -> (B -> C)", "A -> B"}, "A -> C", pr.Implicational, pr.NoSystem},
	{[]string{"A -> (B -> C)"}, "(A -> B) -> (A -> C)", pr.Implicational, pr.NoSystem},
	{[]string{"A -> B", "B -> C"}, "A -> C", pr.Implicational, pr.NoSystem},
	{[]string{"(A -> B) -> C"}, "B -> C", pr.Implicational, pr.NoSystem},

	// Implicational theorems, without premises:
	{nil, "A -> A", pr.Implicational, pr.NoSystem},
	{nil, "A -> (B -> A)", pr.Implicational, pr.NoSystem},
	{nil, "(A -> (A -> B)) -> (A -> B)", pr.Implicational, pr.NoSystem},
	{nil, "(A -> (B -> C)) -> (B -> (A -> C))", pr.Implicational, pr.NoSystem},
	{nil, "(A -> (B -> C)) -> ((A -> B) -> (A -> C))", pr.Implicational, pr.NoSystem},
	{nil, "(A -> B) -> ((B -> C) -> (A -> C))", pr.Implicational, pr.NoSystem},
	{nil, "((A -> B) -> C) -> (B -> C)", pr.Implicational, pr.NoSystem},

	// Positive theorems, with premises:
	{[]string{"A", "B"}, "A /\\ B", pr.Positive, pr.NoSystem},
	{[]string{"A", "B"}, "B /\\ A", pr.Positive, pr.NoSystem},
	{[]string{"A /\\ B"}, "A", pr.Positive, pr.NoSystem},
	{[]string{"A /\\ B"}, "B", pr.Positive, pr.NoSystem},
	{[]string{"A"}, "A \\/ B", pr.Positive, pr.NoSystem},
	{[]string{"A"}, "B \\/ A", pr.Positive, pr.NoSystem},
	{[]string{"A \\/ B", "A -> C", "B -> C"}, "C", pr.Positive, pr.NoSystem},
	{[]string{"B \\/ A", "A -> C", "B -> C"}, "C", pr.Positive, pr.NoSystem},
	{[]string{"A \\/ B", "A -> C"}, "C \\/ B", pr.Positive, pr.NoSystem},
	{[]string{"A \\/ B", "B -> C"}, "A \\/ C", pr.Positive, pr.NoSystem},
	{[]string{"A -> B", "B -> A"}, "A <-> B", pr.Positive, pr.NoSystem},
	{[]string{"A -> B", "B -> A"}, "B <-> A", pr.Positive, pr.NoSystem},
	{[]string{"A <-> B"}, "A -> B", pr.Positive, pr.NoSystem},
	{[]string{"A <-> B"}, "B -> A", pr.Positive, pr.NoSystem},

	// Positive theorems, without premises:
	{nil, "A -> (B -> (A /\\ B))", pr.Positive, pr.NoSystem},
	{nil, "(A /\\ B) -> A", pr.Positive, pr.NoSystem},
	{nil, "(A /\\ B) -> B", pr.Positive, pr.NoSystem},
	{nil, "A -> (A \\/ B)", pr.Positive, pr.NoSystem},
	{nil, "B -> (A \\/ B)", pr.Positive, pr.NoSystem},
	{nil, "(A -> C) -> ((B -> C) -> ((A \\/ B) -> C))", pr.Positive, pr.NoSystem},
	{nil, "(B -> C) -> ((A -> C) -> ((A \\/ B) -> C))", pr.Positive, pr.NoSystem},
	{nil, "(A -> C) -> ((A \\/ B) -> (C \\/ B))", pr.Positive, pr.NoSystem},
	{nil, "(B -> C) -> ((A \\/ B) -> (A \\/ C))", pr.Positive, pr.NoSystem},
	{nil, "(A \\/ B) -> ((A -> C) -> (C \\/ B))", pr.Positive, pr.NoSystem},
	{nil, "(A \\/ B) -> ((B -> C) -> (A \\/ C))", pr.Positive, pr.NoSystem},
	{nil, "(A -> B) -> ((B -> A) -> (A <-> B))", pr.Positive, pr.NoSystem},
	{nil, "(B -> A) -> ((A -> B) -> (A <-> B))", pr.Positive, pr.NoSystem},
	{nil, "(A <-> B) -> (A -> B)", pr.Positive, pr.NoSystem},
	{nil, "(A <-> B) -> (B -> A)", pr.Positive, pr.NoSystem},

	// Minimal theorems, with premises:
	{[]string{"A", "~A"}, "#", pr.Minimal, pr.NoSystem},
	{[]string{"~A", "A"}, "#", pr.Minimal, pr.NoSystem},
	{[]string{"A -> B", "~B"}, "~A", pr.Minimal, pr.NoSystem},
	{[]string{"~A"}, "A -> #", pr.Minimal, pr.NoSystem},
	{[]string{"A"}, "~A -> #", pr.Minimal, pr.NoSystem},

	// Minimal theorems, without premises.
	{nil, "(A /\\ ~A) -> #", pr.Minimal, pr.NoSystem},
	{nil, "A -> (~A -> #)", pr.Minimal, pr.NoSystem},
	{nil, "~A -> (A -> #)", pr.Minimal, pr.NoSystem},
	{nil, "# -> ~A", pr.Minimal, pr.NoSystem},

	// Intuitionistic theorems, with premises:
	{[]string{"#"}, "A", pr.Intuitionistic, pr.NoSystem},

	// Intuitionistic theorems, without premises:
	{nil, "# -> A", pr.Intuitionistic, pr.NoSystem},

	// Classical theorems, with premises:
	{[]string{"~~A"}, "A", pr.Classical, pr.NoSystem},

	// Classical theorems, without premises:
	{nil, "~~A -> A", pr.Classical, pr.NoSystem},
	{nil, "A \\/ ~A", pr.Classical, pr.NoSystem},

	// Quantificational theorems, with premises:
	{[]string{"@x(Ax -> Bx)", "@x(Bx -> Cx)"}, "@x(Ax -> Cx)", pr.Positive, pr.NoSystem},
	{[]string{"@xAax"}, "Aaa", pr.Positive, pr.NoSystem},
	{[]string{"@xAax"}, "Aab", pr.Positive, pr.NoSystem},
	{[]string{"Aaa"}, "$xAxx", pr.Positive, pr.NoSystem},
	{[]string{"Aaa"}, "$xAax", pr.Positive, pr.NoSystem},

	// Quantificational theorems, without premises:
	{nil, "@xAx -> @yAy", pr.Positive, pr.NoSystem},
	{nil, "@xAx -> Aa", pr.Positive, pr.NoSystem},
	{nil, "@xAx -> $xAx", pr.Positive, pr.NoSystem},
	{nil, "Aa -> $xAx", pr.Positive, pr.NoSystem},
	{nil, "@x(Ax -> Bx) -> ($yAy -> $yBy)", pr.Positive, pr.NoSystem},

	// Positive Modal Logic, with premises:
	{nil, "[]^", pr.Positive, pr.NoSystem},
	{[]string{"[](A -> B)"}, "[]A -> []B", pr.Positive, pr.NoSystem},
	{[]string{"[](A -> B)"}, "<>A -> <>B", pr.Positive, pr.NoSystem},

	// Positive Modal Logic, without premises:
	{nil, "[]^", pr.Positive, pr.NoSystem},
	{nil, "[](A -> B) -> ([]A -> []B)", pr.Positive, pr.NoSystem},
	{nil, "[](A -> B) -> (<>A -> <>B)", pr.Positive, pr.NoSystem},

	// Minimal Modal Logic, with premises:
	{[]string{"<>#"}, "#", pr.Minimal, pr.NoSystem},
	{[]string{"<>A"}, "~[]~A", pr.Minimal, pr.NoSystem},

	// Minimal Modal Logic, without premises:
	{nil, "<># -> #", pr.Minimal, pr.NoSystem},
	{nil, "<>A->~[]~A", pr.Minimal, pr.NoSystem},

	// Minimal Modal Logic, without premises:
	{nil, "~<>#", pr.Minimal, pr.NoSystem},
	{nil, "<># -> #", pr.Minimal, pr.NoSystem},

	// Classical Modal Logic, with premises:
	{[]string{"~[]~A"}, "<>A", pr.Classical, pr.NoSystem},
	// {[]string{"<>(A\\/B)"}, "<>A\\/<>B", pr.Classical, pr.NoSystem} // NOTE: Underivable.

	// Classical Modal Logic, without premises:
	{nil, "<>A<->~[]~A", pr.Classical, pr.NoSystem},

	// Modal KD, with premises:
	{[]string{"[]A"}, "<>A", pr.Positive, pr.SystemKD},

	// Modal KD, without premises:
	{nil, "[]A -> <>A", pr.Positive, pr.SystemKD},

	// Modal KM, with premises:
	{[]string{"A"}, "<>A", pr.Positive, pr.SystemKM},
	{[]string{"[]A"}, "A", pr.Positive, pr.SystemKM},

	// Modal KM, without premises:
	{nil, "A -> <>A", pr.Positive, pr.SystemKM},
	{nil, "[]A -> A", pr.Positive, pr.SystemKM},

	// Modal K4, with premises:
	{[]string{"[]A"}, "[][]A", pr.Positive, pr.SystemK4},
	{[]string{"<><>A"}, "<>A", pr.Positive, pr.SystemK4},

	// Modal K4, without premises:
	{nil, "[]A -> [][]A", pr.Positive, pr.SystemK4},
	{nil, "<><>A -> <>A", pr.Positive, pr.SystemK4},

	// Modal KB, with premises:
	{[]string{"A"}, "[]<>A", pr.Positive, pr.SystemKB},
	{[]string{"<>[]A"}, "A", pr.Positive, pr.SystemKB},

	// Modal KB, without premises:
	{nil, "A -> []<>A", pr.Positive, pr.SystemKB},
	{nil, "<>[]A -> A", pr.Positive, pr.SystemKB},
}

func TestNDTheorems(t *testing.T) {
	var (
		tc    testCase
		goal  *fmla.WffTree
		prems []*fmla.WffTree
		prf   *pr.Proof
		drv   *Derivation
		s     string
	)

	for _, tc = range tcs {
		t.Logf("\nAttempting to derive %q from %q.", tc.goal, tc.prems)

		prems = ndTestParseWffs(t, tc.prems...)

		goal = ndTestParseWff(t, tc.goal)

		prf = pr.NewProof(goal, prems...)

		drv = &Derivation{Prf: prf, InfS: tc.infS, ModS: tc.modS, Met: false}

		if !drv.deriveAtStrength() {
			s = drv.Prf.ConvertToFitchString()

			t.Logf("\n%s", s)

			t.Fatalf("FAILED: Did not derive %q from %q.", tc.goal, tc.prems)
		}

		if drv.InfS != tc.infS {
			t.Fatalf("FAILED: Expected inference strength %q, got %q.", tc.infS, drv.InfS)
		}

		if drv.ModS != tc.modS {
			t.Fatalf("FAILED: Expected modal strength %q, got %q.", tc.modS, drv.ModS)
		}

		_ = drv.Prf.MinimizeProof()

		s = drv.Prf.ConvertToFitchString()

		t.Logf("\nPASSED!\n%s", s)
	}
}
