package fmla

func DeepCopy(wff *WffTree) (wffC *WffTree) {
	if wff != nil {
		wffC = &WffTree{
			kind: wff.kind,
			mop:  wff.mop,
			pv:   wff.pv,
			av:   wff.av,
			pred: wff.pred,
			args: wff.args,
			subL: DeepCopy(wff.subL),
			subR: DeepCopy(wff.subR),
			sup:  nil, // The parent is set below.
			h:    wff.h,
		}

		if wffC.subL != nil {
			wffC.subL.sup = wffC
		}

		if wffC.subR != nil {
			wffC.subR.sup = wffC
		}
	}

	return
}

func ReplacePreds(wff *WffTree, pA Predicate, pB Predicate) (wffR *WffTree) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	wffR = DeepCopy(wff)

	switch wffR.kind {
	case Atomic:
		if wffR.pred == pA {
			wffR.pred = pB
		}
	case Unary:
		wffR.subL = ReplacePreds(wffR.subL, pA, pB)
	case Binary:
		wffR.subL = ReplacePreds(wffR.subL, pA, pB)

		wffR.subR = ReplacePreds(wffR.subR, pA, pB)
	case Quantified:
		wffR.subL = ReplacePreds(wffR.subL, pA, pB)
	default:
		panic("Invalid WffTree")
	}

	wffR.h = hashWff(wffR)

	return
}

func ReplaceArgs(wff *WffTree, aA Argument, aB Argument) (wffR *WffTree) {
	var (
		arg     Argument
		newArgs ArgString
	)

	if wff == nil {
		panic("Invalid WffTree")
	}

	wffR = DeepCopy(wff)

	switch wffR.kind {
	case Atomic:
		newArgs = ArgString("")

		for _, arg = range argStringToArgs(wffR.args) {
			if arg == aA {
				newArgs += ArgString(aB)
			} else {
				newArgs += ArgString(arg)
			}
		}

		wffR.args = newArgs
	case Unary:
		wffR.subL = ReplaceArgs(wffR.subL, aA, aB)
	case Binary:
		wffR.subL = ReplaceArgs(wffR.subL, aA, aB)

		wffR.subR = ReplaceArgs(wffR.subR, aA, aB)
	case Quantified:
		wffR.subL = ReplaceArgs(wffR.subL, aA, aB)
	default:
		panic("Invalid WffTree")
	}

	wffR.h = hashWff(wffR)

	return wffR
}

func singleReplacements(s ArgString, aA Argument, aB Argument) (ss []ArgString) {
	var (
		args []Argument
		arg  Argument
		dex  int
	)

	args = argStringToArgs(s)

	for dex, arg = range args {
		if arg == aA {
			s = argsToArgString(args[:dex]...) +
				ArgString(aB) +
				argsToArgString(args[dex+1:]...)

			ss = append(ss, s)
		}
	}

	return
}

func ReplaceEachArgOnce(wff *WffTree, aA Argument, aB Argument) (wffsR []*WffTree) {
	var (
		wffC, sub, wffN *WffTree
		subLs, subRs    []*WffTree
		ss              []ArgString
		s               ArgString
	)

	if wff == nil {
		panic("Invalid WffTree")
	}

	if wff.sup == nil {
		wffC = DeepCopy(wff)
	} else {
		wffC = wff
	}

	switch wffC.kind {
	case Atomic:
		ss = singleReplacements(wffC.args, aA, aB)

		for _, s = range ss {
			wffN = &WffTree{
				kind: Atomic,
				mop:  wffC.mop,
				pv:   wffC.pv,
				av:   wffC.av,
				pred: wffC.pred,
				args: s,
				subL: DeepCopy(wffC.subL),
				subR: DeepCopy(wffC.subR),
				sup:  wffC.sup,
			}

			wffN.h = hashWff(wffN)

			wffsR = append(wffsR, wffN)
		}
	case Unary:
		subLs = ReplaceEachArgOnce(wffC.subL, aA, aB)

		for _, sub = range subLs {
			wffN = NewCompositeWff(wffC.mop, sub, nil, 0, 0)

			wffsR = append(wffsR, wffN)
		}
	case Binary:
		subLs = ReplaceEachArgOnce(wffC.subL, aA, aB)

		for _, sub = range subLs {
			wffN = NewCompositeWff(wffC.mop, sub, wffC.subR, 0, 0)

			wffsR = append(wffsR, wffN)
		}

		subRs = ReplaceEachArgOnce(wffC.subR, aA, aB)

		for _, sub = range subRs {
			wffN = NewCompositeWff(wffC.mop, wffC.subL, sub, 0, 0)

			wffsR = append(wffsR, wffN)
		}
	case Quantified:
		subLs = ReplaceEachArgOnce(wffC.subL, aA, aB)

		for _, sub = range subLs {
			wffN = NewCompositeWff(wffC.mop, sub, nil, wffC.pv, wffC.av)

			wffsR = append(wffsR, wffN)
		}
	default:
		panic("Invalid WffTree")
	}

	return
}

func IsIdentical(wffA, wffB *WffTree) (is bool) {
	is = wffA.h == wffB.h

	return
}

func ReplaceWff(wff, wffA, wffB *WffTree) (wffR *WffTree) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	if wff.sup == nil {
		wffR = DeepCopy(wff)
	} else {
		wffR = wff
	}

	if IsIdentical(wffR, wffA) {
		wffR = &WffTree{
			kind: Atomic,
			mop:  wffB.mop,
			pv:   wffB.pv,
			av:   wffB.av,
			pred: wffB.pred,
			args: wffB.args,
			subL: DeepCopy(wffB.subL),
			subR: DeepCopy(wffB.subR),
			sup:  wffR.sup,
		}

		if wffR.subL != nil {
			wffR.subL.sup = wffR
		}

		if wffR.subR != nil {
			wffR.subR.sup = wffR
		}
	} else {
		switch wffR.kind {
		case Atomic:
			// There are no sub-formulae to check.
		case Unary, Quantified:
			wffR.subL = ReplaceWff(wffR.subL, wffA, wffB)
		case Binary:
			wffR.subL = ReplaceWff(wffR.subL, wffA, wffB)

			wffR.subR = ReplaceWff(wffR.subR, wffA, wffB)
		default:
			panic("Invalid WffTree")
		}
	}

	wffR.h = hashWff(wffR)

	return
}

func GetAllSubformulae(wff *WffTree) (swffs []*WffTree) {
	var (
		swffsL, swffsR []*WffTree
	)

	wff = DeepCopy(wff)

	swffs = append(swffs, wff)

	switch wff.kind {
	case Atomic:
	case Unary:
		swffsL = GetAllSubformulae(wff.subL)

		swffs = append(swffs, swffsL...)
	case Binary:
		swffsL = GetAllSubformulae(wff.subL)

		swffsR = GetAllSubformulae(wff.subR)

		swffs = append(swffs, swffsL...)
		swffs = append(swffs, swffsR...)
	case Quantified:
		swffsL = GetAllSubformulae(wff.subL)

		swffs = append(swffs, swffsL...)
	default:
		panic("Invalid WffTree")
	}

	return
}

func Instantiate(wff *WffTree, pred Predicate, arg Argument) (wffI *WffTree) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	if wff.kind != Quantified {
		panic("WffTree is not a quantified formula.")
	}

	switch {
	case wff.pv != 0 && pred != 0:
		wffI = ReplacePreds(wff.subL, wff.pv, pred)
	case wff.av != 0 && arg != 0:
		wffI = ReplaceArgs(wff.subL, wff.av, arg)
	default:
		panic("Parameters cannot qualify for instantiation.")
	}

	return
}

func GeneralizePred(mop Symbol, wff *WffTree, pc, pv Predicate) (wffP *WffTree) {
	var subL *WffTree

	if wff == nil {
		panic("Invalid WffTree")
	}

	if mop != Exists && mop != ForAll {
		panic("Invalid symbol for generalization.")
	}

	if pc != 0 && pv != 0 {
		subL = ReplacePreds(wff, pc, pv)

		wffP = NewCompositeWff(mop, subL, nil, pv, 0)
	} else {
		panic("Parameters cannot qualify for generalization.")
	}

	return
}

func GeneralizeArg(mop Symbol, wff *WffTree, arg, aVar Argument) (wffA *WffTree) {
	var subL *WffTree

	if wff == nil {
		panic("Invalid WffTree")
	}

	if mop != Exists && mop != ForAll {
		panic("Invalid symbol for generalization.")
	}

	if arg != 0 && aVar != 0 {
		subL = ReplaceArgs(wff, arg, aVar)

		wffA = NewCompositeWff(mop, subL, nil, 0, aVar)
	} else {
		panic("Parameters cannot qualify for generalization.")
	}

	return
}
