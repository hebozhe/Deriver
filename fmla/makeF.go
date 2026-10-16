package fmla

import (
	"slices"
)

func NewAtomicWff(pred Predicate, args ...Argument) (wff *Wff) {
	var (
		lenA int
	)

	if lenA = len(args); pred == Equal && lenA != 2 {
		panic("Equality predicate requires exactly two arguments.")
	} else if (pred == Top || pred == Bot) && lenA != 0 {
		panic("Top and bottom predicates require zero arguments.")
	}

	wff = &Wff{
		kind: Atomic,
		mop:  NoSym,
		pred: pred,
		args: append([]Argument{}, args...),
	}

	wff.hash = hashWff(wff)

	return
}

func newCompositeWff(sym Symbol, subL, subR *Wff, pv Predicate, av Argument) (wff *Wff) {
	switch sym {
	case Neg, Box, Dmd:
		wff = &Wff{
			kind: Unary,
			mop:  sym,
			subL: subL.DeepCopy(),
		}

		wff.subL.sup = wff
	case Vee, Wedge, To, Iff:
		wff = &Wff{
			kind: Binary,
			mop:  sym,
			subL: subL.DeepCopy(),
			subR: subR.DeepCopy(),
		}

		wff.subL.sup, wff.subR.sup = wff, wff
	case ForAll, Exists:
		wff = &Wff{
			kind: Quantified,
			mop:  sym,
			subL: subL.DeepCopy(),
		}

		if pv != NoPred {
			wff.pv = pv
		} else {
			wff.av = av
		}

		wff.subL.sup = wff
	}

	wff.hash = hashWff(wff)

	return
}

func NewUnaryWff(sym Symbol, subL *Wff) (wff *Wff) {
	if subL == nil {
		panic("Missing subformula.")
	}

	switch sym {
	case Neg, Box, Dmd:
		wff = newCompositeWff(sym, subL, nil, NoPred, NoArg)
	default:
		panic("Invalid unary operator.")
	}

	return
}

func NewBinaryWff(sym Symbol, subL, subR *Wff) (wff *Wff) {
	if subL == nil || subR == nil {
		panic("Missing subformulae.")
	}

	switch sym {
	case Vee, Wedge, To, Iff:
		wff = newCompositeWff(sym, subL, subR, NoPred, NoArg)
	default:
		panic("Invalid binary operator.")
	}

	return
}

func NewQuantifiedWff(sym Symbol, subL *Wff, pv Predicate, av Argument) (wff *Wff) {
	if subL == nil {
		panic("Missing subformula.")
	}

	if pv != NoPred && av != NoArg {
		panic("Ambiguous variable over which to quantify.")
	}

	if pv == NoPred && av == NoArg {
		panic("No variable over which to quantify.")
	}

	if pv != NoPred && !slices.Contains(PredVars, pv) {
		panic("Invalid predicate variable.")
	}

	if av != NoArg && !slices.Contains(ArgVars, av) {
		panic("Invalid argument variable.")
	}

	switch sym {
	case ForAll, Exists:
		wff = newCompositeWff(sym, subL, nil, pv, av)
	default:
		panic("Invalid quantifier.")
	}

	return
}
