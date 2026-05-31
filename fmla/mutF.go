package fmla

import (
	"slices"
)

func DeepCopy(wff *Wff) (wffC *Wff) {
	if wff != nil {
		wffC = &Wff{
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

func ReplacePreds(wff *Wff, pA Predicate, pB Predicate) (wffR *Wff) {
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

func ReplaceArgs(wff *Wff, aA Argument, aB Argument) (wffR *Wff) {
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

func ReplaceEachArgOnce(wff *Wff, aA Argument, aB Argument, barOps ...Symbol) (wffsR []*Wff) {
	var (
		has             bool
		wffC, sub, wffN *Wff
		subLs, subRs    []*Wff
		ss              []ArgString
		s               ArgString
	)

	if wff == nil {
		panic("Invalid WffTree")
	}

	if has = slices.Contains(barOps, wff.mop); !has {
		if wff.sup == nil {
			wffC = DeepCopy(wff)
		} else {
			wffC = wff
		}

		switch wffC.kind {
		case Atomic:
			ss = singleReplacements(wffC.args, aA, aB)

			for _, s = range ss {
				wffN = &Wff{
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
	}

	return
}

func ReplaceWff(wff, wffA, wffB *Wff) (wffR *Wff) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	if wff.sup == nil {
		wffR = DeepCopy(wff)
	} else {
		wffR = wff
	}

	if IsIdentical(wffR, wffA) {
		wffR = &Wff{
			kind: wffB.kind,
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

func ReplaceEachWffOnce(wff, wffA, wffB *Wff, barOps ...Symbol) (wffsR []*Wff) {
	var (
		has             bool
		wffC, sub, wffN *Wff
		subLs, subRs    []*Wff
	)

	if wff == nil {
		panic("Invalid WffTree")
	}

	if wff.sup == nil {
		wffC = DeepCopy(wff)
	} else {
		wffC = wff
	}

	if IsIdentical(wffC, wffA) {
		wffN = DeepCopy(wffB)

		wffsR = append(wffsR, wffN)
	} else if has = slices.Contains(barOps, wff.mop); !has {
		switch wffC.kind {
		case Atomic:
		case Unary:
			if IsIdentical(wffC.subL, wffA) {
				wffN = NewCompositeWff(wffC.mop, wffB, nil, 0, 0)

				wffsR = append(wffsR, wffN)
			}

			subLs = ReplaceEachWffOnce(wffC.subL, wffA, wffB, barOps...)

			for _, sub = range subLs {
				wffN = NewCompositeWff(wffC.mop, sub, nil, 0, 0)

				wffsR = append(wffsR, wffN)
			}
		case Binary:
			if IsIdentical(wffC.subL, wffA) {
				wffN = NewCompositeWff(wffC.mop, wffB, wffC.subR, 0, 0)

				wffsR = append(wffsR, wffN)
			}

			subLs = ReplaceEachWffOnce(wffC.subL, wffA, wffB, barOps...)

			for _, sub = range subLs {
				wffN = NewCompositeWff(wffC.mop, sub, wffC.subR, 0, 0)

				wffsR = append(wffsR, wffN)
			}

			if IsIdentical(wffC.subR, wffA) {
				wffN = NewCompositeWff(wffC.mop, wffC.subL, wffB, 0, 0)

				wffsR = append(wffsR, wffN)
			}

			subRs = ReplaceEachWffOnce(wffC.subR, wffA, wffB, barOps...)

			for _, sub = range subRs {
				wffN = NewCompositeWff(wffC.mop, wffC.subL, sub, 0, 0)

				wffsR = append(wffsR, wffN)
			}
		case Quantified:
			if IsIdentical(wffC.subL, wffA) {
				wffN = NewCompositeWff(wffC.mop, wffB, nil, wffC.pv, wffC.av)

				wffsR = append(wffsR, wffN)
			}

			subLs = ReplaceEachWffOnce(wffC.subL, wffA, wffB, barOps...)

			for _, sub = range subLs {
				wffN = NewCompositeWff(wffC.mop, sub, nil, wffC.pv, wffC.av)

				wffsR = append(wffsR, wffN)
			}
		}
	}

	return
}

func GetAllSubformulae(wff *Wff) (swffs []*Wff) {
	var (
		swffsL, swffsR []*Wff
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

func Instantiate(wff *Wff, pred Predicate, arg Argument) (wffI *Wff) {
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

func GeneralizePred(mop Symbol, wff *Wff, pc, pv Predicate) (wffP *Wff) {
	var subL *Wff

	if wff == nil {
		panic("Invalid WffTree")
	}

	if mop != Exists && mop != ForAll {
		panic("Invalid symbol for generalization.")
	}

	if pc != 0 && pv != 0 {
		subL = ReplacePreds(wff, pc, pv)

		wffP = NewCompositeWff(mop, subL, nil, pv, 0)
	} else if pv != 0 {
		wffP = NewCompositeWff(mop, wff, nil, pv, 0)
	} else {
		panic("Parameters cannot qualify for generalization.")
	}

	return
}

func GeneralizeArg(mop Symbol, wff *Wff, ac, av Argument) (wffA *Wff) {
	var subL *Wff

	if wff == nil {
		panic("Invalid WffTree")
	}

	if mop != Exists && mop != ForAll {
		panic("Invalid symbol for generalization.")
	}

	if ac != 0 && av != 0 {
		subL = ReplaceArgs(wff, ac, av)

		wffA = NewCompositeWff(mop, subL, nil, 0, av)
	} else if av != 0 {
		wffA = NewCompositeWff(mop, wff, nil, 0, av)
	} else {
		panic("Parameters cannot qualify for generalization.")
	}

	return
}

func GetAllInstantiations(wff *Wff, pcs []Predicate, acs []Argument) (wffsToWffsI map[*Wff][]*Wff) {
	var (
		pc    Predicate
		ac    Argument
		wffI  *Wff
		wffsI []*Wff
		tmp   map[*Wff][]*Wff
	)

	wffsToWffsI = map[*Wff][]*Wff{}

	if HasOp(wff, Exists) || HasOp(wff, ForAll) {
		switch wff.kind {
		case Unary:
			wffsToWffsI = GetAllInstantiations(wff.subL, pcs, acs)
		case Binary:
			wffsToWffsI = GetAllInstantiations(wff.subL, pcs, acs)

			tmp = GetAllInstantiations(wff.subR, pcs, acs)

			for wff, wffsI = range tmp {
				wffsToWffsI[wff] = append(wffsToWffsI[wff], wffsI...)
			}
		case Quantified:
			if !HasFreeVars(wff.subL) {
				wffI = DeepCopy(wff.subL)

				wffsToWffsI[wff] = append(wffsToWffsI[wff], wffI)
			} else if wff.pv != 0 {
				for _, pc = range pcs {
					wffI = Instantiate(wff, pc, 0)

					wffsToWffsI[wff] = append(wffsToWffsI[wff], wffI)
				}
			} else if wff.av != 0 {
				for _, ac = range acs {
					wffI = Instantiate(wff, 0, ac)

					wffsToWffsI[wff] = append(wffsToWffsI[wff], wffI)
				}
			}

			if HasOp(wff.subL, Exists) || HasOp(wff.subL, ForAll) {
				for _, wffI = range wffsToWffsI[wff] {
					tmp = GetAllInstantiations(wffI, pcs, acs)

					for wff, wffsI = range tmp {
						wffsToWffsI[wff] = append(wffsToWffsI[wff], wffsI...)
					}
				}
			}
		default:
			panic("Invalid WffTree")
		}
	}

	return
}
