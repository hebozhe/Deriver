package pr

import (
	"Deriver/fmla"
	"iter"
)

func allPrfCritsMet(prfO *Prf, prfI *Prf, prcs ...prfCrit) (met, kill bool) {
	var (
		prc prfCrit
	)

	met, kill = true, false

	for _, prc = range prcs {
		if met {
			met, kill = prc(prfO, prfI)
		} else {
			_, kill = prc(prfO, prfI)
		}

		if kill {
			break
		}
	}

	return
}

func (prf *Prf) WalkPrfPairs(critsP ...prfCrit) (prfSeq2 iter.Seq2[*Prf, *Prf]) {
	prfSeq2 = func(yield func(*Prf, *Prf) bool) {
		var walk func(prfI *Prf) (ok bool)

		walk = func(prfI *Prf) (ok bool) {
			var (
				prfO, prfP *Prf
				met, kill  bool
			)

			ok = true

			switch {
			case !prfI.open: // prfI.Close recurses to every leaf proof, so a closed proof has no open inner proofs.
			default:
				for prfO = prfI; prfO != nil; prfO = prfO.prfO {
					if !prfI.open { // prfI.Close invalidates the anchor.
						break
					}

					if met, kill = allPrfCritsMet(prfO, prfI, critsP...); met {
						if !yield(prfO, prfI) { // The consumer halted the walk.
							ok = false

							break
						}

						if kill { // A prfRelCrit killed the current pair iteration.
							break
						}
					} else if kill {
						break
					}
				}

				if ok && prfI.open {
					for _, prfP = range prfI.prfsI {
						if ok = walk(prfP); !ok { // The consumer halted the walk.
							break
						}
					}
				}
			}

			return
		}

		walk(prf)
	}

	return
}

func yieldInstantiations(prf *Prf, wff *fmla.Wff) (wffSeq iter.Seq[*fmla.Wff]) {
	wffSeq = func(yield func(*fmla.Wff) bool) {
		var (
			pv, pc fmla.Predicate
			av, ac fmla.Argument
		)

		if wff.Kind() != fmla.Quantified || wff.IsVacuous() {
			yield(wff)
		} else {
			if yield(wff) {
				if pv, av, _ = wff.Var(); pv != fmla.NoPred {
					for _, pc = range prf.UsedPCs() {
						if !yield(wff.Instantiate(pc)) {
							break
						}
					}
				} else if av != fmla.NoArg {
					for _, ac = range prf.UsedACs() {
						if !yield(wff.Instantiate(ac)) {
							break
						}
					}
				}
			}
		}
	}

	return
}

func (prf *Prf) WalkTargets(critsP ...prfCrit) (prfWffSeq2 iter.Seq2[*Prf, *fmla.Wff]) {
	critsP = append([]prfCrit{}, critsP...)
	critsP = append(critsP, DistPIs(0))

	prfWffSeq2 = func(yield func(*Prf, *fmla.Wff) bool) {
		var (
			prfT       *Prf
			seenPrfsT  map[*Prf]bool
			seenAtPrfT map[fmla.WffHash]bool
			lnT        *Line
			sub, trg   *fmla.Wff
		)

		seenPrfsT = map[*Prf]bool{}

	WALKTARGETS_OUTER:
		for prfT = range prf.WalkPrfPairs(critsP...) {
			if !prfT.open || seenPrfsT[prfT] {
				continue
			}

			seenPrfsT[prfT] = true

			seenAtPrfT = map[fmla.WffHash]bool{}

			for _, sub = range prfT.wffG.AllSubs(true, true) {
				for trg = range yieldInstantiations(prfT, sub) {
					if !seenAtPrfT[trg.Hash()] {
						if yield(prfT, trg) {
							seenAtPrfT[trg.Hash()] = true
						} else {
							break WALKTARGETS_OUTER
						}
					}
				}

			}

			for lnT = range prfT.Lines() {
				if !prfT.open {
					break
				}

				for _, sub = range lnT.wff.AllSubs(true, true) {
					for trg = range yieldInstantiations(prfT, sub) {
						if !seenAtPrfT[trg.Hash()] {
							if yield(prfT, trg) {
								seenAtPrfT[trg.Hash()] = true
							} else {
								break WALKTARGETS_OUTER
							}
						}
					}
				}
			}
		}
	}

	return
}
