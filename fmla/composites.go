package fmla

import (
	"slices"
)

func getLastElement[T any](sl []T) (last T, ok bool) {
	var (
		lenS int
		none T
	)

	if lenS = len(sl); 0 < lenS {
		last, ok = sl[lenS-1], true
	} else {
		last, ok = none, false
	}

	return
}

func NewCompositeWff(sym Symbol, subL, subR *WffTree, pv Predicate, av Argument) (wff *WffTree) {
	switch {
	case slices.Contains(UnaryOps, sym):
		if subL == nil {
			panic("Missing subformula.")
		}

		wff = &WffTree{
			kind: Unary,
			mop:  sym,
			subL: DeepCopy(subL),
		}

		wff.subL.sup = wff
	case slices.Contains(BinaryOps, sym):
		if subL == nil || subR == nil {
			panic("Missing subformulae.")
		}

		wff = &WffTree{
			kind: Binary,
			mop:  sym,
			subL: DeepCopy(subL),
			subR: DeepCopy(subR),
		}

		wff.subL.sup, wff.subR.sup = wff, wff
	case slices.Contains(Quantifiers, sym):
		if pv == 0 && av == 0 {
			panic("No constant over which to quantify.")
		}

		if pv != 0 && av != 0 {
			panic("Ambiguous constants over which to quantify.")
		}

		if subL == nil {
			panic("Missing subformula.")
		}

		wff = &WffTree{
			kind: Quantified,
			mop:  sym,
			subL: DeepCopy(subL),
		}

		if pv != 0 {
			wff.pVar = pv
		} else {
			wff.aVar = av
		}

		wff.subL.sup = wff
	}

	wff.h = hashWff(wff)

	return
}

func NewUnaryChainWff(syms []Symbol, wff *WffTree) (wffC *WffTree) {
	var (
		lenS int
		subL *WffTree
	)

	if wff == nil {
		panic("Invalid WffTree")
	}

	lenS = len(syms)

	switch lenS {
	case 0:
		wffC = DeepCopy(wff)
	case 1:
		if !slices.Contains(UnaryOps, syms[0]) {
			panic("Invalid symbol.")
		}

		wffC = NewCompositeWff(syms[0], wff, nil, 0, 0)
	default:
		if !slices.Contains(UnaryOps, syms[0]) {
			panic("Invalid symbol.")
		}

		subL = NewUnaryChainWff(syms[1:], wff)

		wffC = NewCompositeWff(syms[0], subL, nil, 0, 0)
	}

	return
}

func BuildCompositeWffs(nest uint, domP uint, domA uint, arity uint) (wffs chan *WffTree) {
	switch nest {
	case 0:
		wffs = BuildMixedAtomicWffs(domP, domA, arity)
	default:
		wffs = make(chan *WffTree)

		go func(n, dP, dA, ity uint) {
			var (
				subsL, subsR chan *WffTree
				subL, subR   *WffTree
				sym          Symbol
				pc           Predicate
				ac           Argument
			)

			subsL = BuildCompositeWffs(n-1, dP, dA, ity)

			for subL = range subsL {
				for _, sym = range UnaryOps {
					wffs <- NewCompositeWff(sym, subL, nil, 0, 0)
				}

				for _, sym = range Quantifiers {
					for _, pc = range PredConsts[:dP+1] {
						wffs <- NewCompositeWff(sym, subL, nil, pc, 0)
					}

					for _, ac = range ArgConsts[:dA+1] {
						wffs <- NewCompositeWff(sym, subL, nil, 0, ac)
					}
				}

				subsR = BuildCompositeWffs(n-1, dP, dA, ity)

				for subR = range subsR {
					for _, sym = range BinaryOps {
						wffs <- NewCompositeWff(sym, subL, subR, 0, 0)
					}
				}
			}

			close(wffs)
		}(nest, domP, domA, arity)
	}

	return
}
