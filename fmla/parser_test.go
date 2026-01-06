package fmla

import (
	"testing"
)

func TestConvertNotation(t *testing.T) {
	type testCase struct {
		sIn, sOut string
		exp       bool
	}

	var (
		tcs []testCase
		tc  testCase
		s   string
		ok  bool
	)

	tcs = []testCase{
		// Single-character conversions:
		{"~A", "¬A", true},
		{"$xFx", "∃xFx", true},
		{"@xFx", "∀xFx", true},
		{"^", "⊤", true},
		{"#", "⊥", true},
		{"{A}", "(A)", true},
		{"[A]", "(A)", true},

		// Two-character conversions:
		{"A -> B", "A→B", true},
		{"A /\\ B", "A∧B", true},
		{"A \\/ B", "A∨B", true},
		{"[]A", "□A", true},
		{"<>A", "◇A", true},

		// Three-character conversions:
		{"A <-> B", "A↔B", true},

		// Multiple conversions:
		{"~(A /\\ B) -> C", "¬(A∧B)→C", true},
		{"[](A -> B) <-> (<>A-><>B)", "□(A→B)↔(◇A→◇B)", true},

		// Zero conversions:
		{"A∧B", "A∧B", true},
		{"¬A", "¬A", true},

		// Invalid conversions:
		{"A->>B", "A→>B", false},
		{"A=>B", "A=>B", false},
		{"A<=>B", "A<=>B", false},
		{"A&B", "A&B", false},
	}

	for _, tc = range tcs {
		if s, ok = convertNotation(tc.sIn); s == tc.sOut && ok == tc.exp {
			switch ok {
			case true:
				t.Logf("\nPASSED: Detected valid conversion: %q to %q.", tc.sIn, tc.sOut)
			case false:
				t.Logf("\nPASSED: Detected invalid charaters: %q to %q.", tc.sIn, tc.sOut)
			}
		} else if s != tc.sOut {
			t.Errorf("\nFAILED: Expected %q from %q, got %q.", tc.sOut, tc.sIn, s)

			break
		} else if ok != tc.exp {
			t.Errorf("\nFAILED: Expected %t, got %t.", tc.exp, ok)

			break
		}
	}
}

func TestNewParser(t *testing.T) {
	type testCase struct {
		s   string
		exp bool
	}

	var (
		tcs []testCase
		tc  testCase
		ok  bool
	)

	tcs = []testCase{
		// Valid parses:
		{"A", true},
		{"(A)", true},
		{"((A))", true},
		{"(A ∧ B)", true},
		{"((A ∧ B) ∨ C)", true},
		{"¬(A)", true},
		{"□(A → B)", true},

		// Invalid parses:
		{"", false},
		{"(", false},
		{")", false},
		{"(", false},
		{"(A", false},
		{"A)", false},
		{"(()", false},
		{"())", false},
	}

	for _, tc = range tcs {
		if _, ok = newParser(tc.s); ok == tc.exp {
			switch ok {
			case true:
				t.Logf("\nPASSED: Detected valid parse: %q.", tc.s)
			case false:
				t.Logf("\nPASSED: Detected invalid parse: %q.", tc.s)
			}
		} else {
			t.Errorf("\nFAILED: Expected %t from %q, got %t.", tc.exp, tc.s, ok)

			break
		}
	}
}

func TestParseStringToWff(t *testing.T) {
	type testCase struct {
		s   string
		exp bool
		mop Symbol
	}

	var (
		tcs []testCase
		tc  testCase
		wff *WffTree
		ok  bool
		mop Symbol
	)

	tcs = []testCase{
		// Well-formed atomic formulae:
		{"A", true, NoSymbol},
		{"(A)", true, NoSymbol},
		{"((A))", true, NoSymbol},
		{"Aa", true, NoSymbol},
		{"Aabcdefghijklmnopqrst", true, NoSymbol},
		{"⊤", true, NoSymbol},
		{"⊥", true, NoSymbol},
		{"a=b", true, NoSymbol},
		{"b=a", true, NoSymbol},

		// Ill-formed atomic formulae, according to the grammar:
		{"", false, NoSymbol},
		{"AB", false, NoSymbol},
		{"U", false, NoSymbol},
		{"Ax", false, NoSymbol},
		{"A(abc)", false, NoSymbol},
		{"x=y", false, NoSymbol},
		{"a!=b", false, NoSymbol},
		{"=ab", false, NoSymbol},
		{"A=B", false, NoSymbol},
		{"⊤ab", false, NoSymbol},
		{"a=A", false, NoSymbol},
		{"a==b", false, NoSymbol},
		{"a=bb", false, NoSymbol},
		{"A()", false, NoSymbol},

		// Well-formed unary-chained formulae:
		{"¬A", true, Neg},
		{"□A", true, Box},
		{"◇A", true, Diamond},
		{"¬¬A", true, Neg},
		{"□◇¬A", true, Box},
		{"¬(¬(A))", true, Neg},

		// Ill-formed unary-chained formulae:
		{"¬", false, Neg},
		{"¬()", false, Neg},
		{"¬¬", false, Neg},
		{"□", false, Box},
		{"A□", false, Box},
		{"◇", false, Diamond},
		{"A◇", false, Diamond},

		// Well-formed binary-chained formulae:
		{"A∧B", true, Wedge},
		{"A∨B", true, Vee},
		{"A→B", true, To},
		{"A↔B", true, Iff},
		{"(A→B)", true, To},
		{"(A∧B)→C", true, To},
		{"A→(B∨C)", true, To},

		// Ill-formed binary-chained formulae:
		{"A∧", false, Wedge},
		{"A∨", false, Vee},
		{"A→", false, To},
		{"A↔", false, Iff},
		{"∧B", false, Wedge},
		{"∨B", false, Vee},
		{"→B", false, To},
		{"↔B", false, Iff},
		{"A∧B∧C", false, Wedge}, // Binary ambiguity is not allowed.
		{"A→B→C", false, To},

		// Well-formed quantified formulae:
		{"∀x⊤", true, ForAll},
		{"∃xA", true, Exists},
		{"∃UA", true, Exists},
		{"∀xFx", true, ForAll},
		{"∃xFx", true, Exists},
		{"∃xRab", true, Exists},
		{"∀x∃yx=y", true, ForAll},
		{"∃x∀yRxy", true, Exists},
		{"∀x∃xRxb", true, ForAll},
		{"∀x((Rab))", true, ForAll},
		{"∀x(Fx→Gx)", true, ForAll},
		{"∀x∃y(x=y)", true, ForAll},
		{"∀X∃yXy", true, ForAll},
		{"∀X∃yXay", true, ForAll},

		// Ill-formed quantified formulae:
		{"∀Fx", false, ForAll},
		{"∀x", false, ForAll},
		{"∃xPya", false, Exists},
		{"∀x(x=y)", false, ForAll},
		{"∀X∃YXY", false, ForAll},
		{"∀X∃YXaY", false, ForAll},

		// Well-formed mixed formulae:
		{"¬A∧B", true, Wedge}, // Binary operators precede unary operators.
		{"A∧□B", true, Wedge},
		{"¬(A∧B)", true, Neg},
		{"□∀xFx", true, Box},
		{"∀x□Fx", true, ForAll},
		{"(A→B)∧(C→D)", true, Wedge},
		{"◇(A∨¬B)", true, Diamond},
		{"∀U(U→U)", true, ForAll},
		{"∃V(⊥→V)", true, Exists},
		{"∀X∀x∀y(Xxy↔Xyx)", true, ForAll},
		{"∀X◇(¬X→A)", true, ForAll},

		// Ill-formed mixed formulae:
		{"A¬B∨C", false, Vee},
		{"(A→B)∨(C□→D)", false, Vee},
		{"∀P(P→P)", false, ForAll},
		{"∃P(⊥→P)", false, Exists},
		{"∀R(¬R→A)", false, ForAll},
	}

	for _, tc = range tcs {
		if wff, ok = ParseStringToWff(tc.s); ok == tc.exp {
			if wff != nil {
				if mop = GetWffMop(wff); mop != tc.mop {
					t.Errorf("\nFAILED: Expected main operator %q from %q, got %q.", tc.mop, tc.s, mop)

					break
				}
			}

			switch ok {
			case true:
				t.Logf("\nPASSED: Detected well-formed parse: %q.", tc.s)
			case false:
				t.Logf("\nPASSED: Detected ill-formed parse: %q.", tc.s)
			}
		} else {
			t.Errorf("\nFAILED: Expected %t from %q, got %t.", tc.exp, tc.s, ok)

			break
		}
	}
}

func TestRoundTrip(t *testing.T) {
	var (
		ss         []string
		sA, sB     string
		wffA, wffB *WffTree
		ok         bool
	)

	ss = []string{
		"A",
		"⊤",
		"a=b",
		"¬¬A",
		"□◇¬A",
		"A→(B∨C)",
		"(A∧B)→C",
		"¬(A∧B)",
		"∀xFx",
		"∃xRab",
		"∀x∃y(x=y)",
		"∀U(U→U)",
		"∃V(⊥→V)",
		"∀X∀xXx",
		"∀X∃yXay",
		"□∀xFx",
		"∀X◇(¬X→A)",
		"∀X∀x((Xx→A)∧(A→Xx))",
	}

	for _, sA = range ss {
		if wffA, ok = ParseStringToWff(sA); !ok {
			t.Errorf("\nFAILED: Failed to parse %q.", sA)

			break
		}

		sB = GetWffString(wffA)

		if wffB, ok = ParseStringToWff(sB); !ok {
			t.Errorf("\nFAILED: Failed to parse %q.", sA)

			break
		}

		if !IsIdentical(wffA, wffB) {
			t.Errorf("\nFAILED: %q and %q are not identical by their hashes.", sA, sB)

			break
		}
	}
}
