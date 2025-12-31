package fmla

import "slices"

func orderAtomics(wff *WffTree) (atoms []*WffTree) {
	var (
		atomsL, atomsR []*WffTree
	)

	switch wff.kind {
	case Atomic:
		atoms = []*WffTree{wff}
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

func IsCanonical(wff *WffTree) (is bool) {
	var (
		pcDex, acDex uint
		atoms        []*WffTree
		atom         *WffTree
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

func MakeCanonical(wff *WffTree) (cwff *WffTree) {
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
	var buildMaps func(wt *WffTree)

	buildMaps = func(wt *WffTree) {
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
			if wt.pVar != 0 {
				if _, ok = pvMap[wt.pVar]; !ok && pvDex < lenPV {
					pvMap[wt.pVar] = PredVars[pvDex]

					pvDex += 1
				}
			}

			if wt.aVar != 0 {
				if _, ok = avMap[wt.aVar]; !ok && avIdx < lenAV {
					avMap[wt.aVar] = ArgVars[avIdx]

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

	var applyMaps func(wt *WffTree)

	applyMaps = func(wt *WffTree) {
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
			if wt.pVar != 0 {
				wt.pVar = pvMap[wt.pVar]
			}
			if wt.aVar != 0 {
				wt.aVar = avMap[wt.aVar]
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

func KeepCanonicalWffs(wffs chan *WffTree) (cwffs chan *WffTree) {
	cwffs = make(chan *WffTree)

	go func() {
		var (
			wff *WffTree
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
