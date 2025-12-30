package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
)

func isNotTrivialAtom(pc fmla.Predicate) (does bool) {
	does = pc != fmla.Top && pc != fmla.Bot && pc != fmla.Equals

	return
}

func collectInnerProofs(prf *pr.Proof) (prfsI []*pr.Proof) {
	var (
		purps [6]pr.NDRule
		purp  pr.NDRule
	)

	purps = [6]pr.NDRule{
		pr.ToIntro, pr.NegIntro,
		pr.ForAllIntro, pr.ExistsElim,
		pr.BoxIntro, pr.DiamondElim,
	}

	for _, purp = range purps {
		prfsI = append(prfsI, prf.GetInnerProofs(purp)...)
	}

	return
}

func setInnerIntroProofsRec(prf *pr.Proof) (added uint) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
	)

	prfsI = collectInnerProofs(prf)

	for _, prfI = range prfsI {
		added += SetInnerIntroProofs(prfI) + setInnerIntroProofsRec(prfI)
	}

	return
}

func SetInnerIntroProofs(prf *pr.Proof) (added uint) {
	var (
		goals                           []*fmla.WffTree
		lenG                            int
		goal, subL, subR, ipWff, ipGoal *fmla.WffTree
		mop                             fmla.Symbol
		pv, pc, apc                     fmla.Predicate
		av, ac, aac                     fmla.Argument
	)

	goals = prf.GetAllGoals()

	lenG = len(goals)

	for 0 < lenG {
		goal, goals = goals[0], goals[1:]

		mop, pv, av = fmla.GetWffMopAndVars(goal)

		switch mop {
		case fmla.NoSymbol:
			if pc, _, _ = fmla.GetWffPredAndArgs(goal); isNotTrivialAtom(pc) {
				// For MPL and CPL, add an inner proof for the double-negation of the goal.
				ipWff = fmla.NewCompositeWff(fmla.Neg, goal, nil, 0, 0)

				ipGoal = fmla.NewAtomicWff(fmla.Bot)

				added += prf.AddUniqueInnerProof(ipWff, ipGoal, pr.NegIntro)
			}
		case fmla.Neg:
			ipWff, _ = fmla.GetWffSubformulae(goal)

			ipGoal = fmla.NewAtomicWff(fmla.Bot)

			added += prf.AddUniqueInnerProof(ipWff, ipGoal, pr.NegIntro)
		case fmla.Wedge:
			subL, subR = fmla.GetWffSubformulae(goal)

			goals = append(goals, subL, subR)
		case fmla.Vee:
			subL, subR = fmla.GetWffSubformulae(goal)

			// For CPL, add an inner proof for the double-negation of the goal,
			// because we can reject the disjunction property.
			ipWff = fmla.NewUnaryChainWff([]fmla.Symbol{fmla.Neg, fmla.Neg}, goal)

			goals = append(goals, subL, subR, ipWff)
		case fmla.To:
			ipWff, ipGoal = fmla.GetWffSubformulae(goal)

			added += prf.AddUniqueInnerProof(ipWff, ipGoal, pr.ToIntro)
		case fmla.Iff:
			subL, subR = fmla.GetWffSubformulae(goal)

			ipWff = fmla.NewCompositeWff(fmla.To, subL, subR, 0, 0)

			goals = append(goals, ipWff)

			ipWff = fmla.NewCompositeWff(fmla.To, subR, subL, 0, 0)

			goals = append(goals, ipWff)
		case fmla.Exists:
			// NOTE: This seems like overkill, so revisit this later.
			switch {
			case pv != 0:
				for _, pc = range fmla.PredConsts {
					ipWff = fmla.Instantiate(goal, pc, 0)

					goals = append(goals, ipWff)
				}
			case av != 0:
				for _, ac = range fmla.ArgConsts {
					ipWff = fmla.Instantiate(goal, 0, ac)

					goals = append(goals, ipWff)
				}
			default:
				panic("Invalid WffTree")
			}
		case fmla.ForAll:
			switch {
			case pv != 0:
				ipWff = fmla.NewAtomicWff(fmla.Top)

				apc, _ = prf.MustSelectArbConsts()

				ipGoal = fmla.Instantiate(ipWff, apc, 0)

				added += prf.AddUniqueInnerProof(ipWff, ipGoal, pr.ForAllIntro)
			case av != 0:
				ipWff = fmla.NewAtomicWff(fmla.Top)

				_, aac = prf.MustSelectArbConsts()

				ipGoal = fmla.Instantiate(ipWff, 0, aac)

				added += prf.AddUniqueInnerProof(ipWff, ipGoal, pr.ForAllIntro)
			default:
				panic("Invalid WffTree")
			}
		case fmla.Box:
			ipWff = fmla.NewAtomicWff(fmla.Top)

			ipGoal, _ = fmla.GetWffSubformulae(goal)

			added += prf.AddUniqueInnerProof(ipWff, ipGoal, pr.BoxIntro)
		case fmla.Diamond:
			ipWff = fmla.NewUnaryChainWff([]fmla.Symbol{fmla.Neg, fmla.Box}, goal)

			goals = append(goals, ipWff)
		}

		lenG = len(goals)
	}

	// Traverse the inner proofs, themselves, for further inner proofs
	// to those inner proofs' goals.
	added += setInnerIntroProofsRec(prf)

	return
}

func setInnerElimProofsRec(prf *pr.Proof) (added uint) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
	)

	prfsI = collectInnerProofs(prf)

	for _, prfI = range prfsI {
		added += SetInnerElimProofs(prfI) + setInnerElimProofsRec(prfI)
	}

	return
}

func SetInnerElimProofs(prf *pr.Proof) (added uint) {
	var (
		lns           []*pr.Line
		ln            *pr.Line
		li            *pr.LineInfo
		pv, apc       fmla.Predicate
		av, aac       fmla.Argument
		ipWff, ipGoal *fmla.WffTree
	)

	lns = prf.GetLocalLines()

	for _, ln = range lns {
		li = ln.GetLineInfo()

		switch li.Mop {
		case fmla.Exists:
			_, pv, av = fmla.GetWffMopAndVars(li.Wff)

			switch {
			case pv != 0:
				apc, _ = prf.MustSelectArbConsts()

				ipWff = fmla.Instantiate(li.Wff, apc, 0)

				ipGoal = prf.GetAllGoals()[0]

				added += prf.AddUniqueInnerProof(ipWff, ipGoal, pr.ExistsElim)
			case av != 0:
				_, aac = prf.MustSelectArbConsts()

				ipWff = fmla.Instantiate(li.Wff, 0, aac)

				ipGoal = fmla.NewAtomicWff(fmla.Top)

				added += prf.AddUniqueInnerProof(ipWff, ipGoal, pr.ExistsElim)
			default:
				panic("Invalid WffTree")
			}
		case fmla.Diamond:
			ipWff, _ = fmla.GetWffSubformulae(li.Wff)

			ipGoal = fmla.NewAtomicWff(fmla.Top)

			added += prf.AddUniqueInnerProof(ipWff, ipGoal, pr.DiamondElim)
		}
	}

	// Traverse the inner proofs, themselves, for further inner proofs
	// to those inner proofs' goals.
	added += setInnerElimProofsRec(prf)

	return
}
