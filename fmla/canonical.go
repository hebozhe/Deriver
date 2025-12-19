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

		for _, ac = range atom.args {
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
