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

func AllSubformulae(wff *WffTree) (swffs []*WffTree) {
	var (
		swffsL, swffsR []*WffTree
	)

	wff = DeepCopy(wff)

	swffs = append(swffs, wff)

	switch wff.kind {
	case Atomic:
	case Unary:
		swffsL = AllSubformulae(wff.subL)

		swffs = append(swffs, swffsL...)
	case Binary:
		swffsL = AllSubformulae(wff.subL)

		swffsR = AllSubformulae(wff.subR)

		swffs = append(swffs, swffsL...)
		swffs = append(swffs, swffsR...)
	case Quantified:
		swffsL = AllSubformulae(wff.subL)

		swffs = append(swffs, swffsL...)
	default:
		panic("Invalid WffTree")
	}

	return
}
