package fmla

import (
	"slices"
)

func DeepCopy(wff *WffTree) (cwff *WffTree) {
	if wff != nil {
		cwff = &WffTree{
			kind: wff.kind,
			mop:  wff.mop,
			pVar: wff.pVar,
			aVar: wff.aVar,
			pred: wff.pred,
			args: append([]Argument{}, wff.args...),
			subL: DeepCopy(wff.subL),
			subR: DeepCopy(wff.subR),
			sup:  nil, // The parent is set below.
		}

		if cwff.subL != nil {
			cwff.subL.sup = cwff
		}

		if cwff.subR != nil {
			cwff.subR.sup = cwff
		}
	}

	return
}

func ReplacePreds(wff *WffTree, pA Predicate, pB Predicate) (rwff *WffTree) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	if wff.sup == nil {
		rwff = DeepCopy(wff)
	} else {
		rwff = wff
	}

	switch rwff.kind {
	case Atomic:
		if rwff.pred == pA {
			rwff.pred = pB
		}
	case Unary:
		rwff.subL = ReplacePreds(rwff.subL, pA, pB)
	case Binary:
		rwff.subL = ReplacePreds(rwff.subL, pA, pB)

		rwff.subR = ReplacePreds(rwff.subR, pA, pB)
	case Quantified:
		rwff.subL = ReplacePreds(rwff.subL, pA, pB)
	default:
		panic("Invalid WffTree")
	}

	return
}

func ReplaceArgs(wff *WffTree, aA Argument, aB Argument) (rwff *WffTree) {
	var (
		dex int
	)

	if wff == nil {
		panic("Invalid WffTree")
	}

	if wff.sup == nil {
		rwff = DeepCopy(wff)
	} else {
		rwff = wff
	}

	switch wff.kind {
	case Atomic:
		for dex = range wff.args {
			if wff.args[dex] == aA {
				wff.args[dex] = aB
			}
		}
	case Unary:
		wff.subL = ReplaceArgs(wff.subL, aA, aB)
	case Binary:
		wff.subL = ReplaceArgs(wff.subL, aA, aB)

		wff.subR = ReplaceArgs(wff.subR, aA, aB)
	case Quantified:
		wff.subL = ReplaceArgs(wff.subL, aA, aB)
	default:
		panic("Invalid WffTree")
	}

	rwff = wff

	return
}

func Identical(wffA, wffB *WffTree) (is bool) {
	if is = wffA.kind == wffB.kind; is {
		switch wffA.kind {
		case Atomic:
			is = wffA.pred == wffB.pred &&
				slices.Equal(wffA.args, wffB.args)
		case Unary:
			is = wffA.mop == wffB.mop &&
				Identical(wffA.subL, wffB.subL)
		case Binary:
			is = wffA.mop == wffB.mop &&
				Identical(wffA.subL, wffB.subL) &&
				Identical(wffA.subR, wffB.subR)
		case Quantified:
			is = wffA.pVar == wffB.pVar &&
				wffA.aVar == wffB.aVar &&
				Identical(wffA.subL, wffB.subL)
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
