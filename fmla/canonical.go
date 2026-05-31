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
		panic("Invalid WffTree")
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

func MakeCanonical(wff *Wff) (cwff *Wff) {
	var (
		pcMap, pvMap               map[Predicate]Predicate
		acMap, avMap               map[Argument]Argument
		pcDex, pvDex, acDex, avIdx int
		lenPC, lenPV, lenAC, lenAV int
	)

	pcMap = map[Predicate]Predicate{}
	pvMap = map[Predicate]Predicate{}

	acMap = map[Argument]Argument{}
	avMap = map[Argument]Argument{}

	lenPC, lenPV, lenAC, lenAV = len(PredConsts), len(PredVars), len(ArgConsts), len(ArgVars)

	// Pass 1: Traverse the tree to build the replacement mappings
	var buildMaps func(wt *Wff)

	buildMaps = func(wt *Wff) {
		var (
			ok   bool
			args []Argument
			arg  Argument
		)

		if wt == nil {
			panic("Invalid WffTree")
		}

		switch wt.kind {
		case Atomic:
			// Only map predicase constants and variables, not Top, Bot, or Equals.
			if slices.Contains(PredConsts, wt.pred) {
				if _, ok = pcMap[wt.pred]; !ok && pcDex < lenPC {
					pcMap[wt.pred] = PredConsts[pcDex]

					pcDex += 1
				}
			}

			if slices.Contains(PredVars, wt.pred) {
				if _, ok = pvMap[wt.pred]; !ok && pvDex < lenPV {
					pvMap[wt.pred] = PredVars[pvDex]

					pvDex += 1
				}
			}

			// Map Argument constants and variables.
			args = argStringToArgs(wt.args)

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
			buildMaps(wt.subL)
		case Binary:
			buildMaps(wt.subL)
			buildMaps(wt.subR)
		case Quantified:
			if wt.pv != 0 {
				if _, ok = pvMap[wt.pv]; !ok && pvDex < lenPV {
					pvMap[wt.pv] = PredVars[pvDex]

					pvDex += 1
				}
			}

			if wt.av != 0 {
				if _, ok = avMap[wt.av]; !ok && avIdx < lenAV {
					avMap[wt.av] = ArgVars[avIdx]

					avIdx += 1
				}
			}

			buildMaps(wt.subL)
		default:
			panic("Invalid WffTree")
		}
	}

	buildMaps(wff)

	cwff = DeepCopy(wff)

	var applyMaps func(wt *Wff)

	applyMaps = func(wt *Wff) {
		var (
			mpc, mpv Predicate
			mac, mav Argument
			ok       bool
			args     []Argument
			arg      Argument
			dex      int
		)

		if wt == nil {
			panic("Invalid WffTree")
		}

		switch wt.kind {
		case Quantified:
			if wt.pv != 0 {
				wt.pv = pvMap[wt.pv]
			}
			if wt.av != 0 {
				wt.av = avMap[wt.av]
			}

			applyMaps(wt.subL)
		case Atomic:
			if mpc, ok = pcMap[wt.pred]; ok {
				wt.pred = mpc
			} else if mpv, ok = pvMap[wt.pred]; ok {
				wt.pred = mpv
			}

			args = argStringToArgs(wt.args)

			for dex, arg = range args {
				if mac, ok = acMap[arg]; ok {
					args[dex] = mac
				} else if mav, ok = avMap[arg]; ok {
					args[dex] = mav
				}
			}

			wt.args = argsToArgString(args...)
		case Unary:
			applyMaps(wt.subL)
		case Binary:
			applyMaps(wt.subL)
			applyMaps(wt.subR)
		}
	}

	applyMaps(cwff)

	cwff.h = hashWff(cwff)

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
