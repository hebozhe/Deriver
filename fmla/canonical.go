package fmla

import "slices"

func orderAtomics(wff *Wff) (atoms []*Wff) {
	var (
		atomsL, atomsR []*Wff
	)

	switch wff.kind {
	case Atomic:
		atoms = []*Wff{wff}
	case Unary, Quantified:
		atoms = orderAtomics(wff.subL)
	case Binary:
		atomsL = orderAtomics(wff.subL)

		atomsR = orderAtomics(wff.subR)

		atoms = append(atomsL, atomsR...)
	default:
		panic("The Wff is ill-formed.")
	}

	return
}

func IsCanonical(wff *Wff) (is bool) {
	var (
		pcDex, acDex uint
		atoms        []*Wff
		atom         *Wff
		ac           Argument
	)

	is = true

	atoms = orderAtomics(wff)

ISCANONICAL_OUTER:
	for _, atom = range atoms {
		if atom.pred == Top || atom.pred == Bot {
			continue
		}

		if slices.Contains(PredConsts, atom.pred) && PredConsts[pcDex] < atom.pred {
			is = false

			break
		} else {
			pcDex += 1
		}

		for _, ac = range argStringToArgs(atom.args) {
			if slices.Contains(ArgConsts, ac) && ArgConsts[acDex] < ac {
				is = false

				break ISCANONICAL_OUTER
			} else {
				acDex += 1
			}
		}
	}

	return
}

func MakeCanonical(wff *Wff) (wffC *Wff) {
	var (
		pcMap, pvMap               map[Predicate]Predicate
		acMap, avMap               map[Argument]Argument
		pcDex, pvDex, acDex, avIdx int
		lenPC, lenPV, lenAC, lenAV int
		buildMaps, applyMaps       func(wffK *Wff)
	)

	pcMap = map[Predicate]Predicate{}
	pvMap = map[Predicate]Predicate{}

	acMap = map[Argument]Argument{}
	avMap = map[Argument]Argument{}

	lenPC, lenPV, lenAC, lenAV = len(PredConsts), len(PredVars), len(ArgConsts), len(ArgVars)

	buildMaps = func(wffK *Wff) {
		var (
			ok   bool
			args []Argument
			arg  Argument
		)

		if wffK == nil {
			panic("The Wff is ill-formed.")
		}

		switch wffK.kind {
		case Atomic:
			// Only map predicase constants and variables, not Top, Bot, or Equals.
			if slices.Contains(PredConsts, wffK.pred) {
				if _, ok = pcMap[wffK.pred]; !ok && pcDex < lenPC {
					pcMap[wffK.pred] = PredConsts[pcDex]

					pcDex += 1
				}
			}

			if slices.Contains(PredVars, wffK.pred) {
				if _, ok = pvMap[wffK.pred]; !ok && pvDex < lenPV {
					pvMap[wffK.pred] = PredVars[pvDex]

					pvDex += 1
				}
			}

			// Map Argument constants and variables.
			args = argStringToArgs(wffK.args)

			for _, arg = range args {
				switch {
				case slices.Contains(ArgConsts, arg):
					if _, ok = acMap[arg]; !ok && acDex < lenAC {
						acMap[arg] = ArgConsts[acDex]

						acDex += 1
					}
				case slices.Contains(ArgVars, arg):
					if _, ok = avMap[arg]; !ok && avIdx < len(ArgVars) {
						avMap[arg] = ArgVars[avIdx]

						avIdx += 1
					}
				}
			}
		case Unary:
			buildMaps(wffK.subL)
		case Binary:
			buildMaps(wffK.subL)
			buildMaps(wffK.subR)
		case Quantified:
			if wffK.pv != 0 {
				if _, ok = pvMap[wffK.pv]; !ok && pvDex < lenPV {
					pvMap[wffK.pv] = PredVars[pvDex]

					pvDex += 1
				}
			}

			if wffK.av != 0 {
				if _, ok = avMap[wffK.av]; !ok && avIdx < lenAV {
					avMap[wffK.av] = ArgVars[avIdx]

					avIdx += 1
				}
			}

			buildMaps(wffK.subL)
		default:
			panic("The Wff is ill-formed.")
		}
	}

	buildMaps(wff)

	wffC = DeepCopy(wff)

	applyMaps = func(wffT *Wff) {
		var (
			mpc, mpv Predicate
			mac, mav Argument
			ok       bool
			args     []Argument
			arg      Argument
			dex      int
		)

		if wffT == nil {
			panic("The Wff is ill-formed.")
		}

		switch wffT.kind {
		case Quantified:
			if wffT.pv != 0 {
				wffT.pv = pvMap[wffT.pv]
			}
			if wffT.av != 0 {
				wffT.av = avMap[wffT.av]
			}

			applyMaps(wffT.subL)
		case Atomic:
			if mpc, ok = pcMap[wffT.pred]; ok {
				wffT.pred = mpc
			} else if mpv, ok = pvMap[wffT.pred]; ok {
				wffT.pred = mpv
			}

			args = argStringToArgs(wffT.args)

			for dex, arg = range args {
				if mac, ok = acMap[arg]; ok {
					args[dex] = mac
				} else if mav, ok = avMap[arg]; ok {
					args[dex] = mav
				}
			}

			wffT.args = argsToArgString(args...)
		case Unary:
			applyMaps(wffT.subL)
		case Binary:
			applyMaps(wffT.subL)
			applyMaps(wffT.subR)
		}
	}

	applyMaps(wffC)

	wffC.h = hashWff(wffC)

	return
}

func KeepCanonicalWffs(wffs chan *Wff) (cwffs chan *Wff) {
	cwffs = make(chan *Wff)

	go func() {
		var (
			wff *Wff
		)

		for wff = range wffs {
			if IsCanonical(wff) {
				cwffs <- wff
			}
		}

		close(cwffs)
	}()

	return
}
