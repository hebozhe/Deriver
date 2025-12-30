package fmla

func DeepCopy(wff *WffTree) (wffC *WffTree) {
	if wff != nil {
		wffC = &WffTree{
			kind: wff.kind,
			mop:  wff.mop,
			pVar: wff.pVar,
			aVar: wff.aVar,
			pred: wff.pred,
			args: wff.args,
			subL: DeepCopy(wff.subL),
			subR: DeepCopy(wff.subR),
			sup:  nil, // The parent is set below.
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

	if wff.sup == nil {
		wffR = DeepCopy(wff)
	} else {
		wffR = wff
	}

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

	if wff.sup == nil {
		wffR = DeepCopy(wff)
	} else {
		wffR = wff
	}

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
				pVar: wffC.pVar,
				aVar: wffC.aVar,
				pred: wffC.pred,
				args: s,
				subL: DeepCopy(wffC.subL),
				subR: DeepCopy(wffC.subR),
				sup:  wffC.sup,
			}

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
			wffN = NewCompositeWff(wffC.mop, sub, nil, wffC.pVar, wffC.aVar)

			wffsR = append(wffsR, wffN)
		}
	default:
		panic("Invalid WffTree")
	}

	return
}

func IsIdentical(wffA, wffB *WffTree) (is bool) {
	if is = wffA.kind == wffB.kind; is {
		switch wffA.kind {
		case Atomic:
			is = wffA.pred == wffB.pred &&
				wffA.args == wffB.args
		case Unary:
			is = wffA.mop == wffB.mop &&
				IsIdentical(wffA.subL, wffB.subL)
		case Binary:
			is = wffA.mop == wffB.mop &&
				IsIdentical(wffA.subL, wffB.subL) &&
				IsIdentical(wffA.subR, wffB.subR)
		case Quantified:
			is = wffA.pVar == wffB.pVar &&
				wffA.aVar == wffB.aVar &&
				IsIdentical(wffA.subL, wffB.subL)
		default:
			panic("Invalid WffTree")
		}
	}

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
			pVar: wffB.pVar,
			aVar: wffB.aVar,
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

	return
}

func AllSubformulae(wff *WffTree) (wffs []*WffTree) {
	var (
		swffsL, swffsR []*WffTree
	)

	wff = DeepCopy(wff)

	wffs = append(wffs, wff)

	switch wff.kind {
	case Atomic:
	case Unary:
		swffsL = AllSubformulae(wff.subL)

		wffs = append(wffs, swffsL...)
	case Binary:
		swffsL = AllSubformulae(wff.subL)

		swffsR = AllSubformulae(wff.subR)

		wffs = append(wffs, swffsL...)
		wffs = append(wffs, swffsR...)
	case Quantified:
		swffsL = AllSubformulae(wff.subL)

		wffs = append(wffs, swffsL...)
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
	case wff.pVar != 0 && pred != 0:
		wffI = ReplacePreds(wff, wff.pVar, pred)
	case wff.aVar != 0 && arg != 0:
		wffI = ReplaceArgs(wff, wff.aVar, arg)
	default:
		panic("Parameters cannot qualify for instantiation.")
	}

	return
}

func GeneralizePred(mop Symbol, wff *WffTree, pred, pVar Predicate) (wffP *WffTree) {
	var subL *WffTree

	if wff == nil {
		panic("Invalid WffTree")
	}

	if mop != Exists && mop != ForAll {
		panic("Invalid symbol for generalization.")
	}

	if pred != 0 && pVar != 0 {
		subL = ReplacePreds(wff, pred, pVar)

		wffP = NewCompositeWff(mop, subL, nil, pVar, 0)
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
