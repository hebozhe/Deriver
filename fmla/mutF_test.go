package fmla_test

import (
	"Deriver/fmla"
	"testing"
)

func TestInstantiate(t *testing.T) {
	t.Run("Predicate Variable Instantiated with Predicate Constant", func(t *testing.T) {
		var (
			wffA, wffB *fmla.Wff
		)

		wffA = fmla.MustParseWff("∀UUa")

		wffB = wffA.Instantiate(fmla.Predicate('B'))

		if wffB.String() != "Ba" {
			t.Fatalf("Instantiate() = %q, want %q.", wffB.String(), "Ba")
		}
	})

	t.Run("Argument Variable Instantiated with Argument Constant", func(t *testing.T) {
		var (
			wffA, wffB *fmla.Wff
		)

		wffA = fmla.MustParseWff("∀uAu")

		wffB = wffA.Instantiate(fmla.Argument('b'))

		if wffB.String() != "Ab" {
			t.Fatalf("Instantiate() = %q, want %q.", wffB.String(), "Ab")
		}
	})

	t.Run("Nil WFF Panics", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic calling Instantiate on nil wff.")
			}
		}()

		_ = wff.Instantiate(fmla.Predicate('A'))
	})

	t.Run("Non-Quantified WFF Panics", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic calling Instantiate on a non-quantified wff.")
			}
		}()

		wff = fmla.MustParseWff("Aa")

		_ = wff.Instantiate(fmla.Argument('a'))
	})

	t.Run("Invalid Predicate Constant Panics", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic for a predicate variable in place of a constant.")
			}
		}()

		wff = fmla.MustParseWff("∀UUa")

		_ = wff.Instantiate(fmla.Predicate('U'))
	})

	t.Run("Invalid Argument Constant Panics", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic for an argument variable in place of a constant.")
			}
		}()

		wff = fmla.MustParseWff("∀uAu")

		_ = wff.Instantiate(fmla.Argument('u'))
	})

	t.Run("Missing Predicate Constant for Predicate Variable Panics", func(t *testing.T) {
		var wff *fmla.Wff
		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic supplying an argument constant for a predicate-quantified wff.")
			}
		}()

		wff = fmla.MustParseWff("∀UUa")

		_ = wff.Instantiate(fmla.Argument('b'))
	})

	t.Run("Missing Argument Constant for Argument Variable Panics", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic supplying a predicate constant for an argument-quantified wff.")
			}
		}()

		wff = fmla.MustParseWff("∀uAu")

		_ = wff.Instantiate(fmla.Predicate('B'))
	})

	t.Run("Shadowed Predicate Variable is Ignored", func(t *testing.T) {
		var wffA, wffB *fmla.Wff

		wffA = fmla.MustParseWff("∀U∀UUa")

		if wffB = wffA.Instantiate(fmla.Predicate('B')); wffB.String() != "∀UUa" {
			t.Fatal("Shadowed predicate instantiation failed.")
		}
	})

	t.Run("Shadowed Argument Variable is Ignored", func(t *testing.T) {
		var wffA, wffB *fmla.Wff

		wffA = fmla.MustParseWff("∀u∀uAu")

		if wffB = wffA.Instantiate(fmla.Argument('b')); wffB.String() != "∀uAu" {
			t.Fatal("Shadowed argument instantiation failed.")
		}
	})

	t.Run("0-Valency Fallback During Argument Instantiation", func(t *testing.T) {
		var (
			wffA, wffB *fmla.Wff
		)

		wffA = fmla.MustParseWff("∀u(P∧Au)")

		wffB = wffA.Instantiate(fmla.Argument('b'))

		if wffB.String() != "P∧Ab" {
			t.Fatalf("Instantiate() = %q, want %q.", wffB.String(), "P∧Ab")
		}
	})

	t.Run("Non-Shadowed Quantified Argument Recursion", func(t *testing.T) {
		var (
			wffA, wffB *fmla.Wff
		)

		wffA = fmla.MustParseWff("∀u∀vAuv")

		wffB = wffA.Instantiate(fmla.Argument('b'))

		if wffB.String() != "∀vAbv" {
			t.Fatalf("Instantiate() = %q, want %q.", wffB.String(), "∀vAbv")
		}
	})
}

func TestGeneralize(t *testing.T) {
	t.Run("ForAll over Predicate Constant", func(t *testing.T) {
		var (
			wffA, wffB *fmla.Wff
			wffsB      map[fmla.WffHash]*fmla.Wff
			lenB       int
		)

		wffA = fmla.MustParseWff("Aa")

		wffsB = wffA.Generalize(fmla.Predicate('A'), fmla.Predicate('U'), fmla.ForAll)

		if lenB = len(wffsB); lenB != 1 {
			t.Fatalf("Generalize() returned %d wffs, want 1.", lenB)
		}

		for _, wffB = range wffsB {
			if wffB.String() != "∀UUa" {
				t.Fatalf("Generalize() = %q, want %q.", wffB.String(), "∀UUa")
			}
		}
	})

	t.Run("ForAll over Argument Constant", func(t *testing.T) {
		var (
			wffA, wffB *fmla.Wff
			wffsB      map[fmla.WffHash]*fmla.Wff
			lenB       int
		)

		wffA = fmla.MustParseWff("Aa")

		wffsB = wffA.Generalize(fmla.Argument('a'), fmla.Argument('u'), fmla.ForAll)

		if lenB = len(wffsB); lenB != 1 {
			t.Fatalf("Generalize() returned %d wffs, want 1.", lenB)
		}

		for _, wffB = range wffsB {
			if wffB.String() != "∀uAu" {
				t.Fatalf("Generalize() = %q, want %q.", wffB.String(), "∀uAu")
			}
		}
	})

	t.Run("ForAll Preserves Compound Formulae", func(t *testing.T) {
		var (
			wffA, wffB *fmla.Wff
			wffsB      map[fmla.WffHash]*fmla.Wff
		)

		wffA = fmla.MustParseWff("¬Aa∧(¬Bb↔∃xAax)")

		wffsB = wffA.Generalize(fmla.Predicate('A'), fmla.Predicate('U'), fmla.ForAll)

		for _, wffB = range wffsB {
			if wffB.String() != "∀U(¬Ua∧(¬Bb↔∃xUax))" {
				t.Fatalf("Generalize() = %q, want %q.", wffB.String(), "∀U(¬Ua∧(¬Bb↔∃xUax))")
			}
		}
	})

	t.Run("Exists over Predicate Constant", func(t *testing.T) {
		var (
			wffA  *fmla.Wff
			wffsB map[fmla.WffHash]*fmla.Wff
			lenB  int
		)

		wffA = fmla.MustParseWff("Aa∧Aa")

		wffsB = wffA.Generalize(fmla.Predicate('A'), fmla.Predicate('U'), fmla.Exists)

		if lenB = len(wffsB); lenB != 4 {
			t.Fatalf("Generalize() returned %d wffs, want 4.", lenB)
		}
	})

	t.Run("Exists over Argument Constant", func(t *testing.T) {
		var (
			wffA  *fmla.Wff
			wffsB map[fmla.WffHash]*fmla.Wff
			lenB  int
		)

		wffA = fmla.MustParseWff("Aa")

		wffsB = wffA.Generalize(fmla.Argument('a'), fmla.Argument('u'), fmla.Exists)

		if lenB = len(wffsB); lenB == 0 {
			t.Fatal("Generalize() returned no wffs for Exists.")
		}
	})

	t.Run("Nil WFF Panics", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic calling Generalize on nil wff.")
			}
		}()

		_ = wff.Generalize(fmla.Predicate('A'), fmla.Predicate('U'), fmla.ForAll)
	})

	t.Run("Invalid Operator Panics", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic for a non-quantifier operator.")
			}
		}()

		wff = fmla.MustParseWff("Aa")

		_ = wff.Generalize(fmla.Predicate('A'), fmla.Predicate('U'), fmla.Wedge)
	})

	t.Run("Invalid Predicate Constant Panics", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic for an invalid predicate constant.")
			}
		}()

		wff = fmla.MustParseWff("Aa")

		_ = wff.Generalize(fmla.Predicate('U'), fmla.Predicate('V'), fmla.ForAll)
	})

	t.Run("Invalid Predicate Variable Panics", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic for an invalid predicate variable.")
			}
		}()

		wff = fmla.MustParseWff("Aa")

		_ = wff.Generalize(fmla.Predicate('A'), fmla.Predicate('B'), fmla.ForAll)
	})

	t.Run("Invalid Argument Constant Panics", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic for an invalid argument constant.")
			}
		}()

		wff = fmla.MustParseWff("Aa")

		_ = wff.Generalize(fmla.Argument('u'), fmla.Argument('v'), fmla.ForAll)
	})

	t.Run("Invalid Argument Variable Panics", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic for an invalid argument variable.")
			}
		}()

		wff = fmla.MustParseWff("Aa")

		_ = wff.Generalize(fmla.Argument('a'), fmla.Argument('b'), fmla.ForAll)
	})

	t.Run("ForAll Preserves Compound Formulae over Argument Constant", func(t *testing.T) {
		var (
			wffA, wffB *fmla.Wff
			wffsB      map[fmla.WffHash]*fmla.Wff
		)

		wffA = fmla.MustParseWff("¬Aa∧(¬Ba↔∃xAax)")

		wffsB = wffA.Generalize(fmla.Argument('a'), fmla.Argument('u'), fmla.ForAll)

		for _, wffB = range wffsB {
			if wffB.String() != "∀u(¬Au∧(¬Bu↔∃xAux))" {
				t.Fatalf("Generalize() = %q, want %q.", wffB.String(), "∀u(¬Au∧(¬Bu↔∃xAux))")
			}
		}
	})
}

func TestReplace(t *testing.T) {
	t.Run("Invalid Predicate Constant in First Argument Panics", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic for an invalid predicate constant in first parameter.")
			}
		}()

		wff = fmla.MustParseWff("Aa")

		_ = wff.Replace(fmla.Predicate('?'), fmla.Predicate('B'))
	})

	t.Run("Invalid Predicate Constant in Second Argument Panics", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic for an invalid predicate constant in second parameter.")
			}
		}()

		wff = fmla.MustParseWff("Aa")

		_ = wff.Replace(fmla.Predicate('A'), fmla.Predicate('?'))
	})

	t.Run("Invalid Argument Constant in First Argument Panics", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic for an invalid argument constant in first parameter.")
			}
		}()

		wff = fmla.MustParseWff("Aa")

		_ = wff.Replace(fmla.Argument('?'), fmla.Argument('b'))
	})

	t.Run("Invalid Argument Constant in Second Argument Panics", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic for an invalid argument constant in second parameter.")
			}
		}()

		wff = fmla.MustParseWff("Aa")

		_ = wff.Replace(fmla.Argument('a'), fmla.Argument('?'))
	})

	t.Run("Predicate for Predicate", func(t *testing.T) {
		var (
			wffA  *fmla.Wff
			wffsB map[fmla.WffHash]*fmla.Wff
			lenB  int
		)

		wffA = fmla.MustParseWff("Aa∧Ba")

		wffsB = wffA.Replace(fmla.Predicate('A'), fmla.Predicate('C'))

		if lenB = len(wffsB); lenB == 0 {
			t.Fatal("Replace() returned no wffs.")
		}
	})

	t.Run("Argument for Argument", func(t *testing.T) {
		var (
			wffA  *fmla.Wff
			wffsB map[fmla.WffHash]*fmla.Wff
			lenB  int
		)

		wffA = fmla.MustParseWff("Aa")

		wffsB = wffA.Replace(fmla.Argument('a'), fmla.Argument('b'))

		if lenB = len(wffsB); lenB == 0 {
			t.Fatal("Replace() returned no wffs.")
		}
	})

	t.Run("WFF for WFF", func(t *testing.T) {
		var (
			wffA, wffB, wffC, wffD *fmla.Wff
			wffsD                  map[fmla.WffHash]*fmla.Wff
			found                  bool
			lenD                   int
		)

		wffA, wffB, wffC = fmla.MustParseWff("Aa∧Bb"), fmla.MustParseWff("Aa"), fmla.MustParseWff("Cc")

		wffsD = wffA.Replace(wffB, wffC)

		for _, wffD = range wffsD {
			if found = wffD.String() == "Cc∧Bb"; found {
				break
			}
		}

		if lenD = len(wffsD); lenD == 0 || !found {
			t.Fatalf("Replace() did not produce the expected substitution among %d results.", lenD)
		}
	})

	t.Run("WFF for WFF with Skip Preserves the Skipped Branch", func(t *testing.T) {
		var (
			wffA, wffB, wffC, wffD *fmla.Wff
			wffsD                  map[fmla.WffHash]*fmla.Wff
			lenD                   int
		)

		wffA, wffB, wffC = fmla.MustParseWff("□Aa"), fmla.MustParseWff("Aa"), fmla.MustParseWff("Cc")

		wffsD = wffA.Replace(wffB, wffC, fmla.Box)

		if lenD = len(wffsD); lenD != 1 {
			t.Fatalf("Replace() with skip returned %d wffs, want 1.", lenD)
		}

		for _, wffD = range wffsD {
			if !wffD.Is(wffA) {
				t.Fatalf("Replace() with skip modified a formula under the skipped operator was %q.", wffD.String())
			}
		}
	})

	t.Run("Nil WFF Panics", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic calling Replace on nil wff.")
			}
		}()

		_ = wff.Replace(fmla.Predicate('A'), fmla.Predicate('B'))
	})

	t.Run("Unary Recursion", func(t *testing.T) {
		var (
			wffA, wffB, wffC, wffD *fmla.Wff
			wffsD                  map[fmla.WffHash]*fmla.Wff
			lenD                   int
			finds                  map[string]bool
			s                      string
			seen                   bool
		)

		wffA, wffB, wffC = fmla.MustParseWff("¬Aa"), fmla.MustParseWff("Aa"), fmla.MustParseWff("Cc")

		wffsD = wffA.Replace(wffB, wffC)

		if lenD = len(wffsD); lenD != 2 {
			t.Fatalf("Replace() returned %d wffs, want 2.", lenD)
		}

		finds = map[string]bool{"¬Aa": false, "¬Cc": false}

		for _, wffD = range wffsD {
			finds[wffD.String()] = true
		}

		for s, seen = range finds {
			if !seen {
				t.Fatalf("Replace() never produced expected wff %q.", s)
			}
		}
	})

	t.Run("Quantified Recursion", func(t *testing.T) {
		var (
			wffA, wffB, wffC, wffD *fmla.Wff
			wffsD                  map[fmla.WffHash]*fmla.Wff
			lenD                   int
			finds                  map[string]bool
			s                      string
			seen                   bool
		)

		wffA = fmla.MustParseWff("∀uAu")

		wffB = fmla.NewAtomicWff(fmla.Predicate('A'), fmla.Argument('u'))

		wffC = fmla.NewAtomicWff(fmla.Predicate('C'), fmla.Argument('u'))

		wffsD = wffA.Replace(wffB, wffC)

		if lenD = len(wffsD); lenD != 2 {
			t.Fatalf("Replace() returned %d wffs, want 2.", lenD)
		}

		finds = map[string]bool{"∀uAu": false, "∀uCu": false}

		for _, wffD = range wffsD {
			finds[wffD.String()] = true
		}

		for s, seen = range finds {
			if !seen {
				t.Fatalf("Replace() never produced expected wff %q.", s)
			}
		}
	})

	t.Run("Target Deeper Than Current Node Is a No-Op", func(t *testing.T) {
		var (
			wffA, wffB, wffC, wffD *fmla.Wff
			wffsD                  map[fmla.WffHash]*fmla.Wff
			lenD                   int
		)

		wffA, wffB, wffC = fmla.MustParseWff("Aa"), fmla.MustParseWff("Cc∧Dd"), fmla.MustParseWff("Ee")

		wffsD = wffA.Replace(wffB, wffC)

		if lenD = len(wffsD); lenD != 1 {
			t.Fatalf("Replace() returned %d wffs, want 1.", lenD)
		}

		for _, wffD = range wffsD {
			if !wffD.Is(wffA) {
				t.Fatalf("Replace() modified a wff it could not possibly contain: got %q.", wffD.String())
			}
		}
	})

	t.Run("Argument for Argument with Multi-Arity", func(t *testing.T) {
		var (
			wffA  *fmla.Wff
			wffsB map[fmla.WffHash]*fmla.Wff
			lenB  int
		)

		wffA = fmla.MustParseWff("a=b")

		wffsB = wffA.Replace(fmla.Argument('a'), fmla.Argument('c'))

		if lenB = len(wffsB); lenB != 2 {
			t.Fatalf("Replace() returned %d wffs, want 2.", lenB)
		}
	})

	t.Run("Predicate for Predicate with Skip", func(t *testing.T) {
		var (
			wffA  *fmla.Wff
			wffsB map[fmla.WffHash]*fmla.Wff
			lenB  int
		)

		wffA = fmla.MustParseWff("□Aa")

		wffsB = wffA.Replace(fmla.Predicate('A'), fmla.Predicate('C'), fmla.Box)

		if lenB = len(wffsB); lenB != 1 {
			t.Fatalf("Replace() returned %d wffs, want 1.", lenB)
		}
	})

	t.Run("Argument for Argument with Skip", func(t *testing.T) {
		var (
			wffA  *fmla.Wff
			wffsB map[fmla.WffHash]*fmla.Wff
			lenB  int
		)

		wffA = fmla.MustParseWff("◇Aa")

		wffsB = wffA.Replace(fmla.Argument('a'), fmla.Argument('c'), fmla.Dmd)

		if lenB = len(wffsB); lenB != 1 {
			t.Fatalf("Replace() returned %d wffs, want 1.", lenB)
		}
	})

	t.Run("Predicate for Predicate Not Found", func(t *testing.T) {
		var (
			wffA  *fmla.Wff
			wffsB map[fmla.WffHash]*fmla.Wff
			lenB  int
		)

		wffA = fmla.MustParseWff("Aa")

		wffsB = wffA.Replace(fmla.Predicate('B'), fmla.Predicate('C'))

		if lenB = len(wffsB); lenB != 1 {
			t.Fatalf("Replace() returned %d wffs, want 1.", lenB)
		}
	})

	t.Run("Unary Recursion over Predicate Constant", func(t *testing.T) {
		var (
			wffA, wffB *fmla.Wff
			wffsB      map[fmla.WffHash]*fmla.Wff
			lenB       int
			finds      map[string]bool
			s          string
			seen       bool
		)

		wffA = fmla.MustParseWff("¬Aa")

		wffsB = wffA.Replace(fmla.Predicate('A'), fmla.Predicate('C'))

		if lenB = len(wffsB); lenB != 2 {
			t.Fatalf("Replace() returned %d wffs, want 2.", lenB)
		}

		finds = map[string]bool{"¬Aa": false, "¬Ca": false}

		for _, wffB = range wffsB {
			finds[wffB.String()] = true
		}

		for s, seen = range finds {
			if !seen {
				t.Fatalf("Replace() never produced expected wff %q.", s)
			}
		}
	})

	t.Run("Quantified Recursion over Predicate Constant", func(t *testing.T) {
		var (
			wffA, wffB *fmla.Wff
			wffsB      map[fmla.WffHash]*fmla.Wff
			lenB       int
			finds      map[string]bool
			s          string
			seen       bool
		)

		wffA = fmla.MustParseWff("∀uAu")

		wffsB = wffA.Replace(fmla.Predicate('A'), fmla.Predicate('C'))

		if lenB = len(wffsB); lenB != 2 {
			t.Fatalf("Replace() returned %d wffs, want 2.", lenB)
		}

		finds = map[string]bool{"∀uAu": false, "∀uCu": false}

		for _, wffB = range wffsB {
			finds[wffB.String()] = true
		}

		for s, seen = range finds {
			if !seen {
				t.Fatalf("Replace() never produced expected wff %q.", s)
			}
		}
	})

	t.Run("Shadowed Predicate Variable Halts Recursion", func(t *testing.T) {
		var (
			wffA, wffB *fmla.Wff
			wffsB      map[fmla.WffHash]*fmla.Wff
			lenB       int
		)

		wffA = fmla.MustParseWff("∀UAa")

		wffsB = wffA.Replace(fmla.Predicate('U'), fmla.Predicate('C'))

		if lenB = len(wffsB); lenB != 1 {
			t.Fatalf("Replace() returned %d wffs, want 1.", lenB)
		}

		for _, wffB = range wffsB {
			if wffB.String() != "∀UAa" {
				t.Fatalf("Replace() = %q, want %q.", wffB.String(), "∀UAa")
			}
		}
	})

	t.Run("Unary Recursion over Argument Constant", func(t *testing.T) {
		var (
			wffA, wffB *fmla.Wff
			wffsB      map[fmla.WffHash]*fmla.Wff
			lenB       int
			finds      map[string]bool
			s          string
			seen       bool
		)

		wffA = fmla.MustParseWff("¬Aa")

		wffsB = wffA.Replace(fmla.Argument('a'), fmla.Argument('b'))

		if lenB = len(wffsB); lenB != 2 {
			t.Fatalf("Replace() returned %d wffs, want 2.", lenB)
		}

		finds = map[string]bool{"¬Aa": false, "¬Ab": false}

		for _, wffB = range wffsB {
			finds[wffB.String()] = true
		}

		for s, seen = range finds {
			if !seen {
				t.Fatalf("Replace() never produced expected wff %q.", s)
			}
		}
	})

	t.Run("Binary Recursion over Argument Constant", func(t *testing.T) {
		var (
			wffA, wffB *fmla.Wff
			wffsB      map[fmla.WffHash]*fmla.Wff
			lenB       int
			finds      map[string]bool
			s          string
			seen       bool
		)

		wffA = fmla.MustParseWff("Aa∧Ab")

		wffsB = wffA.Replace(fmla.Argument('a'), fmla.Argument('b'))

		if lenB = len(wffsB); lenB != 2 {
			t.Fatalf("Replace() returned %d wffs, want 2.", lenB)
		}

		finds = map[string]bool{"Aa∧Ab": false, "Ab∧Ab": false}

		for _, wffB = range wffsB {
			finds[wffB.String()] = true
		}

		for s, seen = range finds {
			if !seen {
				t.Fatalf("Replace() never produced expected wff %q.", s)
			}
		}
	})

	t.Run("Quantified Recursion over Argument Constant", func(t *testing.T) {
		var (
			wffA, wffB *fmla.Wff
			wffsB      map[fmla.WffHash]*fmla.Wff
			lenB       int
			finds      map[string]bool
			s          string
			seen       bool
		)

		wffA = fmla.MustParseWff("∀vAa")

		wffsB = wffA.Replace(fmla.Argument('a'), fmla.Argument('b'))

		if lenB = len(wffsB); lenB != 2 {
			t.Fatalf("Replace() returned %d wffs, want 2.", lenB)
		}

		finds = map[string]bool{"∀vAa": false, "∀vAb": false}

		for _, wffB = range wffsB {
			finds[wffB.String()] = true
		}

		for s, seen = range finds {
			if !seen {
				t.Fatalf("Replace() never produced expected wff %q.", s)
			}
		}
	})

	t.Run("Shadowed Argument Variable Halts Recursion", func(t *testing.T) {
		var (
			wffA, wffB *fmla.Wff
			wffsB      map[fmla.WffHash]*fmla.Wff
			lenB       int
		)

		wffA = fmla.MustParseWff("∀uAu")

		wffsB = wffA.Replace(fmla.Argument('u'), fmla.Argument('v'))

		if lenB = len(wffsB); lenB != 1 {
			t.Fatalf("Replace() returned %d wffs, want 1.", lenB)
		}

		for _, wffB = range wffsB {
			if wffB.String() != "∀uAu" {
				t.Fatalf("Replace() = %q, want %q.", wffB.String(), "∀uAu")
			}
		}
	})
}
