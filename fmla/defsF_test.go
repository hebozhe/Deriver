package fmla_test

import (
	"Deriver/fmla"
	"fmt"
	"math/rand/v2"
	"slices"
	"testing"
)

func TestNilWffPanics(t *testing.T) {
	type panicMethod struct {
		name string
		fn   func()
	}

	var (
		wff          *fmla.Wff
		panicMethods []panicMethod
		pm           panicMethod
	)

	t.Run("Nil DeepCopy Returns Nil", func(t *testing.T) {
		var (
			wffC *fmla.Wff
		)

		if wffC = wff.DeepCopy(); wffC != nil {
			t.Fatalf("Expected nil from DeepCopy on nil wff, got %v.", wffC)
		}
	})

	panicMethods = []panicMethod{
		{"Kind", func() { wff.Kind() }},
		{"Mop", func() { wff.Mop() }},
		{"Var", func() { wff.Var() }},
		{"SubL", func() { wff.SubL() }},
		{"SubR", func() { wff.SubR() }},
		{"Subs", func() { wff.Subs() }},
		{"AllSubs", func() { wff.AllSubs(false, false) }},
		{"Hash", func() { wff.Hash() }},
		{"Pred", func() { wff.Pred() }},
		{"Args", func() { wff.Args() }},
		{"Valency", func() { wff.Valency() }},
		{"AllPreds", func() { wff.AllPreds(false) }},
		{"AllArgs", func() { wff.AllArgs(false) }},
		{"AllVars", func() { wff.AllVars(false) }},
		{"AllConsts", func() { wff.AllConsts(false) }},
		{"String", func() { _ = wff.String() }},
		{"Len", func() { wff.Len() }},
		{"Depth", func() { wff.Depth() }},
		{"Is", func() { wff.Is(new(fmla.Wff)) }},
		{"Has", func() { wff.Has(fmla.NoSym) }},
		{"IsClosed", func() { wff.IsClosed() }},
	}

	for _, pm = range panicMethods {
		t.Run(pm.name+" Panic", func(t *testing.T) {
			defer func() {
				var (
					r   any
					msg string
					ok  bool
				)

				if r = recover(); r == nil {
					t.Fatalf("Expected panic calling %s on nil wff.", pm.name)
				}

				if msg, ok = r.(string); !ok || msg != "Missing formula." {
					t.Fatalf("Expected panic %q, got %v.", "Missing formula.", r)
				}
			}()

			pm.fn()
		})
	}
}

func TestAtomicWffMethods(t *testing.T) {
	var (
		wff *fmla.Wff
	)

	wff = fmla.NewAtomicWff(fmla.PredConsts[0], fmla.ArgConsts[0])

	t.Run("Kind", func(t *testing.T) {
		var (
			kind fmla.WffKind
		)

		if kind = wff.Kind(); kind != fmla.Atomic {
			t.Fatalf("Kind() = %v, want %v.", kind, fmla.Atomic)
		}
	})

	t.Run("Pred and Args", func(t *testing.T) {
		var (
			p             fmla.Predicate
			args          []fmla.Argument
			lenA, valency int
		)

		if p = wff.Pred(); p != 'A' {
			t.Fatalf("Pred() = %c, want 'A'.", p)
		}

		args = wff.Args()

		if lenA = len(args); lenA != 1 || args[0] != 'a' {
			t.Fatalf("Args() = %v, want ['a'].", args)
		}

		if valency = wff.Valency(); valency != 1 {
			t.Fatalf("Valency() = %d, want 1.", valency)
		}
	})

	t.Run("Subs and Mop on Atomic", func(t *testing.T) {
		var (
			mop   fmla.Symbol
			subL  *fmla.Wff
			subR  *fmla.Wff
			arity int
		)

		if mop = wff.Mop(); mop != fmla.NoSym {
			t.Fatalf("Mop() = %v, want NoSym.", mop)
		}

		if subL = wff.SubL(); subL != nil {
			t.Fatalf("SubL() = %v, want nil.", subL)
		}

		if subR = wff.SubR(); subR != nil {
			t.Fatalf("SubR() = %v, want nil.", subR)
		}

		if _, _, arity = wff.Subs(); arity != 0 {
			t.Fatalf("Subs() arity = %d, want 0.", arity)
		}
	})

	t.Run("String and Len", func(t *testing.T) {
		var (
			s          string
			lenW, depW uint
		)

		if s = wff.String(); s != "Aa" {
			t.Fatalf("String() = %q, want %q.", s, "Aa")
		}

		if lenW = wff.Len(); lenW != 2 {
			t.Fatalf("Len() = %d, want 2.", lenW)
		}

		if depW = wff.Depth(); depW != 1 {
			t.Fatalf("Depth() = %d, want 1.", depW)
		}
	})

	t.Run("IsClosed and DeepCopy", func(t *testing.T) {
		var (
			wffC *fmla.Wff
		)

		if !wff.IsClosed() {
			t.Fatal("Expected atomic formula 'Aa' to be closed")
		}

		if wffC = wff.DeepCopy(); !wff.Is(wffC) {
			t.Fatalf("DeepCopy hash mismatch: original %v, copy %v.", wff.Hash(), wffC.Hash())
		}
	})
}

func TestWffString(t *testing.T) {
	var (
		top, bot, Aa, Bb, aEqualsb    *fmla.Wff
		newUnary, newBinary, newQuant *fmla.Wff
		s                             string
	)

	top = fmla.NewAtomicWff(fmla.Top)
	bot = fmla.NewAtomicWff(fmla.Bot)
	Aa = fmla.NewAtomicWff(fmla.PredConsts[0], fmla.ArgConsts[0])
	Bb = fmla.NewAtomicWff(fmla.PredConsts[1], fmla.ArgConsts[1])
	aEqualsb = fmla.NewAtomicWff(fmla.Equal, fmla.ArgConsts[0], fmla.ArgConsts[1])

	// Special atomic predicates
	if s = top.String(); s != "⊤" {
		t.Fatalf("top.String() = %q, want %q.", s, "⊤")
	}

	if s = bot.String(); s != "⊥" {
		t.Fatalf("bot.String() = %q, want %q.", s, "⊥")
	}

	// Atomic
	if s = Aa.String(); s != "Aa" {
		t.Fatalf("Aa.String() = %q, want %q.", s, "Aa")
	}

	if s = Bb.String(); s != "Bb" {
		t.Fatalf("Bb.String() = %q, want %q.", s, "Bb")
	}

	if s = aEqualsb.String(); s != "a=b" {
		t.Fatalf("aEqualsb.String() = %q, want %q.", s, "a=b")
	}

	// Nested Unary and Binary.
	newUnary = fmla.NewUnaryWff(fmla.Neg, fmla.NewBinaryWff(fmla.To, Aa, Bb))

	if s = newUnary.String(); s != "¬(Aa→Bb)" {
		t.Fatalf("newUnary.String() = %q, want %q.", s, "¬(Aa→Bb)")
	}

	newBinary = fmla.NewBinaryWff(fmla.Wedge, fmla.NewBinaryWff(fmla.To, Aa, Bb), fmla.NewBinaryWff(fmla.Vee, Aa, Bb))

	if s = newBinary.String(); s != "(Aa→Bb)∧(Aa∨Bb)" {
		t.Fatalf("newBinary.String() = %q, want %q.", s, "(Aa→Bb)∧(Aa∨Bb)")
	}

	// Quantified over Predicate Var.
	newQuant = fmla.NewQuantifiedWff(fmla.ForAll, Aa, fmla.PredVars[0], fmla.NoArg)

	if s = newQuant.String(); s != "∀UAa" {
		t.Fatalf("newQuant.String() = %q, want %q.", s, "∀UAa")
	}

	// Quantified over Argument Var.
	newQuant = fmla.NewQuantifiedWff(fmla.ForAll, Aa, fmla.NoPred, fmla.ArgVars[0])

	if s = newQuant.String(); s != "∀uAa" {
		t.Fatalf("newQuant.String() = %q, want %q.", s, "∀uAa")
	}
}

func randomUintGen(lb, ub uint) (n uint) {
	if ub < lb {
		lb, ub = ub, lb
	}

	n = lb + uint(rand.N(int(ub-lb)+1)) // Inclusive of ub.

	return
}

func randomAtomicWff() (wff *fmla.Wff) {
	var (
		lenP, lenA, dex int
		n               uint
		pred            fmla.Predicate
		args            []fmla.Argument
	)

	lenP, lenA = len(fmla.Preds), len(fmla.Args)

	n = randomUintGen(0, uint(lenP-1))

	pred = fmla.Preds[n]

	switch pred {
	case fmla.Top, fmla.Bot:
		wff = fmla.NewAtomicWff(pred)
	case fmla.Equal:
		args = make([]fmla.Argument, 2)

		for dex = 0; dex < 2; dex += 1 {
			n = randomUintGen(0, uint(lenA-1))

			args[dex] = fmla.Args[n]
		}

		wff = fmla.NewAtomicWff(pred, args...)
	default:
		n = randomUintGen(0, 5)

		args = make([]fmla.Argument, n)

		for dex = range args {
			n = randomUintGen(0, uint(lenA-1))

			args[dex] = fmla.Args[n]
		}

		wff = fmla.NewAtomicWff(pred, args...)
	}

	return
}

func randomWffAtDepth(depth uint) (wff *fmla.Wff) {
	var (
		n          uint
		lenX       int
		subA, subB *fmla.Wff
		pv         fmla.Predicate
		av         fmla.Argument
	)

	if depth < 2 {
		wff = randomAtomicWff()
	} else {
		switch randomUintGen(1, 3) {
		case 1: // Unary: The subformula must carry depth-1.
			subA = randomWffAtDepth(depth - 1)

			lenX = len(fmla.UnaryOps)
			n = randomUintGen(0, uint(lenX-1))

			wff = fmla.NewUnaryWff(fmla.UnaryOps[n], subA)
		case 2: // Binary: One subformula must carry depth-1; the other can carry any depth from 1 to depth-1.
			n = randomUintGen(1, depth-1)

			subA, subB = randomWffAtDepth(depth-1), randomWffAtDepth(n)

			lenX = len(fmla.BinaryOps)
			n = randomUintGen(0, uint(lenX-1))

			switch randomUintGen(1, 2) {
			case 1: // Put subA on the left and subB on the right.
				wff = fmla.NewBinaryWff(fmla.BinaryOps[n], subA, subB)
			case 2: // Put subA on the right and subB on the left.
				wff = fmla.NewBinaryWff(fmla.BinaryOps[n], subB, subA)
			}
		case 3: // Quantified: The subformula must carry depth-1.
			subA = randomWffAtDepth(depth - 1)

			switch randomUintGen(1, 2) {
			case 1: // Quantify over a predicate variable.
				lenX = len(fmla.PredVars)
				n = randomUintGen(0, uint(lenX-1))

				pv = fmla.PredVars[n]

				lenX = len(fmla.Quantifiers)
				n = randomUintGen(0, uint(lenX-1))

				wff = fmla.NewQuantifiedWff(fmla.Quantifiers[n], subA, pv, fmla.NoArg)
			case 2: // Quantify over an argument variable.
				lenX = len(fmla.ArgVars)
				n = randomUintGen(0, uint(lenX-1))

				av = fmla.ArgVars[n]

				lenX = len(fmla.Quantifiers)
				n = randomUintGen(0, uint(lenX-1))

				wff = fmla.NewQuantifiedWff(fmla.Quantifiers[n], subA, fmla.NoPred, av)
			}
		}
	}

	return
}

func totalSubs(wff *fmla.Wff) (tot int) {
	tot = 1

	if wff.SubL() != nil {
		tot += totalSubs(wff.SubL())
	}

	if wff.SubR() != nil {
		tot += totalSubs(wff.SubR())
	}

	return
}

func TestWffCharacteristics(t *testing.T) {
	var (
		wff   *fmla.Wff
		depth uint
		name  string
	)

	// Test depth matches.
	for depth = 1; depth < 21; depth += 1 {
		name = fmt.Sprintf("Test of Random WFF's Depth at Depth %d", depth)

		wff = randomWffAtDepth(depth)

		t.Run(name, func(t *testing.T) {
			var (
				depW uint
			)

			if depW = wff.Depth(); depW != depth {
				t.Fatalf("Depth() = %d, want %d, for wff %q.", depW, depth, wff.String())
			}
		})

		name = fmt.Sprintf(
			"Test of Random WFF's Extracted Hashes, Main Operator, Subformulae, and Arity at Depth %d",
			depth,
		)

		t.Run(name, func(t *testing.T) {
			var (
				subL, subR  *fmla.Wff
				arity, lenS int
				pv          fmla.Predicate
				av          fmla.Argument
				ok          bool
				subs        []*fmla.Wff
			)

			if wff.Hash() == 0 {
				t.Fatalf("Hash() = %d, want non-zero, for wff %q.", wff.Hash(), wff.String())
			}

			switch wff.Mop() {
			case fmla.NoSym:
				if wff.Kind() != fmla.Atomic {
					t.Fatalf("Unexpected Kind %q for wff %q.", wff.Kind(), wff.String())
				}

				if subL, subR, arity = wff.Subs(); arity != 0 {
					t.Fatalf("Mismatched arity of %d for wff %q.", arity, wff.String())
				} else if subL != nil {
					t.Fatalf("Unexpected left subformula %q for wff %q.", wff.SubL().String(), wff.String())
				} else if subR != nil {
					t.Fatalf("Unexpected right subformula %q for wff %q.", wff.SubR().String(), wff.String())
				}
			case fmla.Neg, fmla.Box, fmla.Dmd:
				if wff.Kind() != fmla.Unary {
					t.Fatalf("Unexpected Kind %q for wff %q.", wff.Kind(), wff.String())
				}

				if subL, subR, arity = wff.Subs(); arity != 1 {
					t.Fatalf("Mismatched arity of %d for wff %q.", arity, wff.String())
				} else if subL == nil {
					t.Fatalf("Missing left subformula for wff %q.", wff.String())
				} else if subR != nil {
					t.Fatalf("Unexpected right subformula %q for wff %q.", wff.SubR().String(), wff.String())
				}
			case fmla.Wedge, fmla.Vee, fmla.To, fmla.Iff:
				if wff.Kind() != fmla.Binary {
					t.Fatalf("Unexpected Kind %q for wff %q.", wff.Kind(), wff.String())
				}

				if subL, subR, arity = wff.Subs(); arity != 2 {
					t.Fatalf("Mismatched arity of %d for wff %q.", arity, wff.String())
				} else if subL == nil {
					t.Fatalf("Missing left subformula for wff %q.", wff.String())
				} else if subR == nil {
					t.Fatalf("Missing right subformula for wff %q.", wff.String())
				}
			case fmla.ForAll, fmla.Exists:
				if wff.Kind() != fmla.Quantified {
					t.Fatalf("Unexpected Kind %q for wff %q.", wff.Kind(), wff.String())
				}

				if pv, av, ok = wff.Var(); !ok {
					t.Fatalf("Marked failure in finding variables for wff %q.", wff.String())
				} else if pv != fmla.NoPred && av != fmla.NoArg {
					t.Fatalf("Unexpected variables %q and %q for wff %q.", pv, av, wff.String())
				} else if pv != fmla.NoPred && slices.Index([]rune(wff.String()), rune(pv)) != 1 {
					t.Fatalf("Unexpected binding %q for wff %q.", pv, wff.String())
				} else if av != fmla.NoArg && slices.Index([]rune(wff.String()), rune(av)) != 1 {
					t.Fatalf("Unexpected binding %q for wff %q.", av, wff.String())
				}

				if subL, subR, arity = wff.Subs(); arity != 1 {
					t.Fatalf("Mismatched arity of %d for wff %q.", arity, wff.String())
				} else if subL == nil {
					t.Fatalf("Missing left subformula for wff %q.", wff.String())
				} else if subR != nil {
					t.Fatalf("Unexpected right subformula %q for wff %q.", wff.SubR().String(), wff.String())
				}
			default:
				t.Fatalf("Unexpected Main Operator %q for wff %q.", wff.Mop(), wff.String())
			}

			subs = wff.AllSubs(false, false)

			if lenS = len(subs); lenS != totalSubs(wff) {
				t.Fatalf("Subs(false) returned %d subformulas, expected %d.", lenS, totalSubs(wff))
			}

			subs = wff.AllSubs(true, false)

			if lenS = len(subs); lenS < totalSubs(wff) {
				t.Fatalf("Subs(true) returned %d subformulas, expected at most %d.", lenS, totalSubs(wff))
			}
		})

		name = fmt.Sprintf("Test of Random WFF's Extracted Predicates and Arguments at Depth %d", depth)

		t.Run(name, func(t *testing.T) {
			var (
				pcsP, pvsP, pvsV, pcsC []fmla.Predicate
				acsA, avsA, avsV, acsC []fmla.Argument
			)

			pcsP, pvsP = wff.AllPreds(false)

			acsA, avsA = wff.AllArgs(false)

			pvsV, avsV = wff.AllVars(false)

			pcsC, acsC = wff.AllConsts(false)

			if !slices.Equal(pcsP, pcsC) {
				t.Fatalf("Predicates %q and %q differ.", pcsP, pcsC)
			}

			if !slices.Equal(pvsP, pvsV) {
				t.Fatalf("Predicates %q and %q differ.", pvsP, pvsV)
			}

			if !slices.Equal(acsA, acsC) {
				t.Fatalf("Arguments %q and %q differ.", acsA, acsC)
			}

			if !slices.Equal(avsA, avsV) {
				t.Fatalf("Arguments %q and %q differ.", avsA, avsV)
			}

			pcsP, pvsP = wff.AllPreds(true)

			acsA, avsA = wff.AllArgs(true)

			pvsV, avsV = wff.AllVars(true)

			pcsC, acsC = wff.AllConsts(true)

			if !slices.Equal(pcsP, pcsC) {
				t.Fatalf("Predicates %q and %q differ.", pcsP, pcsC)
			}

			if !slices.Equal(pvsP, pvsV) {
				t.Fatalf("Predicates %q and %q differ.", pvsP, pvsV)
			}

			if !slices.Equal(acsA, acsC) {
				t.Fatalf("Arguments %q and %q differ.", acsA, acsC)
			}

			if !slices.Equal(avsA, avsV) {
				t.Fatalf("Arguments %q and %q differ.", avsA, avsV)
			}
		})
	}
}

func TestWffHas(t *testing.T) {
	var (
		Aa, Bb              *fmla.Wff
		newUnary, newBinary *fmla.Wff
	)

	Aa = fmla.NewAtomicWff(fmla.PredConsts[0], fmla.ArgConsts[0])
	Bb = fmla.NewAtomicWff(fmla.PredConsts[1], fmla.ArgConsts[1])
	newUnary = fmla.NewUnaryWff(fmla.Box, Aa)
	newBinary = fmla.NewBinaryWff(fmla.Wedge, Aa, Bb)

	if !Aa.Has(Aa) {
		t.Fatalf("Expected atomic formula %q to be present in %q.", Aa.String(), Aa.String())
	}

	if !newUnary.Has(Aa) {
		t.Fatalf("Expected atomic formula %q to be present in %q.", Aa.String(), newUnary.String())
	}

	if !newUnary.Has(fmla.Box) {
		t.Fatalf("Expected operator %q to be present in %q.", fmla.Box, newUnary.String())
	}

	if !newUnary.Has(fmla.Predicate('A')) {
		t.Fatalf("Expected predicate %q to be present in %q.", fmla.Predicate('A'), newUnary.String())
	}

	if !newUnary.Has(fmla.Argument('a')) {
		t.Fatalf("Expected argument %q to be present in %q.", fmla.Argument('a'), newUnary.String())
	}

	if newUnary.Has(fmla.ForAll) {
		t.Fatalf("Expected quantifier %q not to be present in %q.", fmla.ForAll, newUnary.String())
	}

	if !newBinary.Has(Aa) {
		t.Fatalf("Expected atomic formula %q to be present in %q.", Aa.String(), newBinary.String())
	}

	if !newBinary.Has(Bb) {
		t.Fatalf("Expected atomic formula %q to be present in %q.", Bb.String(), newBinary.String())
	}

	if !newBinary.Has(fmla.Wedge) {
		t.Fatalf("Expected operator %q to be present in %q.", fmla.Wedge, newBinary.String())
	}

	if newBinary.Has(fmla.ForAll) {
		t.Fatalf("Expected quantifier %q not to be present in %q.", fmla.ForAll, newBinary.String())
	}

	if !newBinary.Has(fmla.Predicate('A')) {
		t.Fatalf("Expected predicate %q to be present in %q.", fmla.Predicate('A'), newBinary.String())
	}

	if !newBinary.Has(fmla.Argument('a')) {
		t.Fatalf("Expected argument %q to be present in %q.", fmla.Argument('a'), newBinary.String())
	}

	if newBinary.Has(fmla.Predicate('Z')) {
		t.Fatalf("Expected predicate %q not to be present in %q.", fmla.Predicate('Z'), newBinary.String())
	}

	if newBinary.Has(fmla.Argument('z')) {
		t.Fatalf("Expected argument %q not to be present in %q.", fmla.Argument('z'), newBinary.String())
	}

	if !newBinary.Has(Aa.String()) {
		t.Fatalf("Expected string %q to be present in %q.", Aa.String(), newBinary.String())
	}

	if !newBinary.Has(Bb.String()) {
		t.Fatalf("Expected string %q to be present in %q.", Bb.String(), newBinary.String())
	}

	if !newBinary.Has('A') {
		t.Fatalf("Expected rune %q to be present in %q.", 'A', newBinary.String())
	}
}
