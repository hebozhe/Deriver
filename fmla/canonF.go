package fmla

import "slices"

type canonMap struct {
	pcs map[Predicate]bool
	pvs map[Predicate]bool
	acs map[Argument]bool
	avs map[Argument]bool
}

func (cm canonMap) add[T Predicate | Argument](this T) (ok bool) {
	var (
		pred Predicate
		arg  Argument
	)

	if pred, ok = any(this).(Predicate); ok && slices.Contains(Preds, pred) {
		if ok = slices.Contains(PredConsts, pred); ok {
			cm.pcs[pred] = true
		} else if ok = slices.Contains(PredVars, pred); ok {
			cm.pvs[pred] = true
		}
	} else if arg, ok = any(this).(Argument); ok && slices.Contains(Args, arg) {
		if ok = slices.Contains(ArgConsts, arg); ok {
			cm.acs[arg] = true
		} else if ok = slices.Contains(ArgVars, arg); ok {
			cm.avs[arg] = true
		}
	}

	return
}

func (cm canonMap) isExpected[T Predicate | Argument](this T) (is bool) {
	var (
		pred Predicate
		arg  Argument
		ok   bool
		lenX int
	)

	if pred, ok = any(this).(Predicate); ok && slices.Contains(Preds, pred) {
		if slices.Contains(PredConsts, pred) {
			lenX = len(cm.pcs)

			is = cm.pcs[pred] || PredConsts[lenX] == pred
		} else if slices.Contains(PredVars, pred) {
			lenX = len(cm.pvs)

			is = cm.pvs[pred] || PredVars[lenX] == pred
		}
	} else if arg, ok = any(this).(Argument); ok && slices.Contains(Args, arg) {
		if slices.Contains(ArgConsts, arg) {
			lenX = len(cm.acs)

			is = cm.acs[arg] || ArgConsts[lenX] == arg
		} else if slices.Contains(ArgVars, arg) {
			lenX = len(cm.avs)

			is = cm.avs[arg] || ArgVars[lenX] == arg
		}
	}

	return
}

type canonRemap struct {
	pcs map[Predicate]Predicate
	pvs map[Predicate]Predicate
	acs map[Argument]Argument
	avs map[Argument]Argument
}

func (crm canonRemap) remap[T Predicate | Argument](this T) (that T) {
	var (
		pred, newP Predicate
		arg, newA  Argument
		ok         bool
		lenX       int
	)

	if pred, ok = any(this).(Predicate); ok && slices.Contains(Preds, pred) {
		if slices.Contains(SpecPredConsts, pred) {
			that = T(pred)
		} else if slices.Contains(PredConsts, pred) {
			if newP, ok = crm.pcs[pred]; ok {
				that = T(newP)
			} else {
				lenX = len(crm.pcs)

				newP, crm.pcs[pred] = PredConsts[lenX], PredConsts[lenX]

				that = T(newP)
			}
		} else if slices.Contains(PredVars, pred) {
			if newP, ok = crm.pvs[pred]; ok {
				that = T(newP)
			} else {
				lenX = len(crm.pvs)

				newP, crm.pvs[pred] = PredVars[lenX], PredVars[lenX]

				that = T(newP)
			}
		}
	} else if arg, ok = any(this).(Argument); ok && slices.Contains(Args, arg) {
		if slices.Contains(ArgConsts, arg) {
			if newA, ok = crm.acs[arg]; ok {
				that = T(newA)
			} else {
				lenX = len(crm.acs)

				newA, crm.acs[arg] = ArgConsts[lenX], ArgConsts[lenX]

				that = T(newA)
			}
		} else if slices.Contains(ArgVars, arg) {
			if newA, ok = crm.avs[arg]; ok {
				that = T(newA)
			} else {
				lenX = len(crm.avs)

				newA, crm.avs[arg] = ArgVars[lenX], ArgVars[lenX]

				that = T(newA)
			}
		}
	}

	return
}

func (crm canonRemap) remapAll[T Predicate | Argument](these ...T) (those []T) {
	var (
		lenT, dex int
		this      T
	)

	lenT = len(these)

	those = make([]T, lenT)

	for dex, this = range these {
		those[dex] = crm.remap(this)
	}

	return
}

func isCanonical(wff *Wff, cm canonMap) (is bool) {
	var (
		arg Argument
	)

	if wff == nil {
		panic("Missing formula.")
	}

	switch wff.kind {
	case Atomic:
		switch wff.pred {
		case Top, Bot:
			is = true
		case Equal:
			is = cm.isExpected(wff.args[0]) && cm.add(wff.args[0]) && cm.isExpected(wff.args[1]) && cm.add(wff.args[1])
		default:
			if is = cm.isExpected(wff.pred) && cm.add(wff.pred); is {
				for _, arg = range wff.args {
					if is = cm.isExpected(arg) && cm.add(arg); !is {
						break
					}
				}
			}
		}
	case Unary:
		is = isCanonical(wff.subL, cm)
	case Binary:
		is = isCanonical(wff.subL, cm) && isCanonical(wff.subR, cm)
	case Quantified:
		if wff.pv != NoPred {
			is = cm.isExpected(wff.pv) && cm.add(wff.pv) && isCanonical(wff.subL, cm)
		} else if wff.av != NoArg {
			is = cm.isExpected(wff.av) && cm.add(wff.av) && isCanonical(wff.subL, cm)
		}
	default:
		panic("Unsupported formula kind.")
	}

	return
}

func makeCanonical(wffA *Wff, crm canonRemap) (wffB *Wff) {
	var (
		pred       Predicate
		arg        Argument
		args       []Argument
		subL, subR *Wff
	)

	if wffA == nil {
		panic("Missing formula.")
	}

	switch wffA.kind {
	case Atomic:
		pred, args = crm.remap(wffA.pred), crm.remapAll(wffA.args...)

		wffB = NewAtomicWff(pred, args...)
	case Unary:
		subL = makeCanonical(wffA.subL, crm)

		wffB = NewUnaryWff(wffA.mop, subL)
	case Binary:
		subL, subR = makeCanonical(wffA.subL, crm), makeCanonical(wffA.subR, crm)

		wffB = NewBinaryWff(wffA.mop, subL, subR)
	case Quantified:
		if wffA.pv != NoPred {
			pred, subL = crm.remap(wffA.pv), makeCanonical(wffA.subL, crm)

			wffB = NewQuantifiedWff(wffA.mop, subL, pred, NoArg)
		} else if wffA.av != NoArg {
			arg, subL = crm.remap(wffA.av), makeCanonical(wffA.subL, crm)

			wffB = NewQuantifiedWff(wffA.mop, subL, NoPred, arg)
		}
	default:
		panic("Unsupported formula kind.")
	}

	return
}

func (wff *Wff) IsCanonical() (is bool) {
	var cm canonMap = canonMap{
		pcs: map[Predicate]bool{},
		pvs: map[Predicate]bool{},
		acs: map[Argument]bool{},
		avs: map[Argument]bool{},
	}

	is = isCanonical(wff, cm)

	return
}

func (wffA *Wff) MakeCanonical() (wffB *Wff) {
	var crm canonRemap = canonRemap{
		pcs: map[Predicate]Predicate{},
		pvs: map[Predicate]Predicate{},
		acs: map[Argument]Argument{},
		avs: map[Argument]Argument{},
	}

	wffB = makeCanonical(wffA, crm)

	return
}
