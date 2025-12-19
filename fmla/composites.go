package fmla

import "slices"

func NewConnectiveWff(con Connective, subL, subR *WffTree) (wff *WffTree) {
	switch {
	case slices.Contains(UnaryOps, con):
		wff = &WffTree{
			kind: Unary,
			mop:  Symbol(con),
			subL: DeepCopy(subL),
		}

		wff.subL.sup = wff
	case slices.Contains(BinaryOps, con):
		wff = &WffTree{
			kind: Binary,
			mop:  Symbol(con),
			subL: DeepCopy(subL),
			subR: DeepCopy(subR),
		}

		wff.subL.sup = wff

		wff.subR.sup = wff
	default:
		panic("Invalid Connective")
	}

	return
}

func highestUnboundVariables(wff *WffTree) (pv Predicate, av Argument) {
	var (
		pvs        []Predicate
		avs        []Argument
		dexP, dexA int
	)

	pvs, avs = GetVariables(wff)

	for dexP = len(PredVars) - 1; -1 < dexP; dexP -= 1 {
		if slices.Contains(pvs, PredVars[dexP]) {
			continue
		}

		pv = PredVars[dexP]

		break
	}

	for dexA = len(ArgVars) - 1; -1 < dexA; dexA -= 1 {
		if slices.Contains(avs, ArgVars[dexA]) {
			continue
		}

		av = ArgVars[dexA]

		break
	}

	return
}

func NewQuantifiedWff(qua Quantifier, subL *WffTree, pc Predicate, ac Argument) (wff *WffTree) {
	var (
		pv Predicate
		av Argument
	)

	if pc != 0 && ac != 0 {
		panic("Ambiguous quantification.")
	}

	if pv, av = highestUnboundVariables(subL); pv == 0 && av == 0 {
		panic("No unbound variables.")
	}

	switch {
	case pc != 0:
		wff = &WffTree{
			kind: Quantified,
			mop:  Symbol(qua),
			pred: pc,
			subL: ReplacePreds(DeepCopy(subL), pv, pc),
		}
	case ac != 0:
		wff = &WffTree{
			kind: Quantified,
			mop:  Symbol(qua),
			aVar: ac,
			subL: ReplaceArgs(DeepCopy(subL), av, ac),
		}
	}

	wff.subL.sup = wff

	return
}

func NewQuantifiedWffs(qua Quantifier, subL *WffTree) (wffs chan *WffTree) {
	var (
		bwff *WffTree
	)

	wffs = make(chan *WffTree)

	// Create a base quantified WffTree.
	bwff = &WffTree{
		kind: Quantified,
		mop:  Symbol(qua),
		subL: DeepCopy(subL),
	}

	go func(t *WffTree) {
		var (
			pv, pc Predicate
			av, ac Argument
			pcs    []Predicate
			acs    []Argument
			wff    *WffTree
		)

		pv, av = highestUnboundVariables(t)

		if pv == 0 && av == 0 {
			panic("At least one unbound variable must be available.")
		}

		if pv != 0 {
			wff = DeepCopy(t)

			wff.pVar = pv

			wffs <- wff
		}

		if av != 0 {
			wff = DeepCopy(t)

			wff.aVar = av

			wffs <- wff
		}

		pcs, acs = GetConstants(t.subL)

		if pv != 0 {
			for _, pc = range pcs {
				wff = DeepCopy(t)

				wff.pVar = pv

				wffs <- ReplacePreds(wff, pc, pv)
			}
		}

		if av != 0 {
			for _, ac = range acs {
				wff = DeepCopy(t)

				wff.aVar = av

				wffs <- ReplaceArgs(wff, ac, av)
			}

		}

		close(wffs)
	}(bwff)

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
				con          Connective
				qtr          Quantifier
				wff          *WffTree
			)

			subsL = BuildCompositeWffs(n-1, dP, dA, ity)

			for subL = range subsL {
				for _, con = range UnaryOps {
					wffs <- NewConnectiveWff(con, subL, nil)
				}

				for _, qtr = range Quantifiers {
					for wff = range NewQuantifiedWffs(qtr, subL) {
						wffs <- wff
					}
				}

				subsR = BuildCompositeWffs(n-1, dP, dA, ity)

				for subR = range subsR {
					for _, con = range BinaryOps {
						wffs <- NewConnectiveWff(con, subL, subR)
					}
				}
			}

			close(wffs)
		}(nest, domP, domA, arity)
	}

	return
}
