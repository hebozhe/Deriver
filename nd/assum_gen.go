package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
)

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

func helpSeedInnerIntroProofs(prf *pr.Proof) (added uint) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
	)

	prfsI = collectInnerProofs(prf)

	for _, prfI = range prfsI {
		added += seedInnerIntroProofs(prfI) + helpSeedInnerIntroProofs(prfI)
	}

	return
}

func seedInnerIntroProofs(prf *pr.Proof) (added uint) {
	var (
		goals                           []*fmla.WffTree
		lns                             []*pr.Line
		ln                              *pr.Line
		li                              *pr.LineInfo
		lenG                            int
		goal, subL, subR, ipWff, ipGoal *fmla.WffTree
		mop                             fmla.Symbol
		pcs                             []fmla.Predicate
		acs                             []fmla.Argument
		pv, pc, apc                     fmla.Predicate
		av, ac, aac                     fmla.Argument
	)

	goals = prf.PopMetSubgoals()

	lenG = len(goals)

	for 0 < lenG {
		goal, goals = goals[0], goals[1:]

		mop, pv, av = fmla.GetWffMopAndVars(goal)

		switch mop {
		case fmla.NoSymbol:
			pc, _, _ = fmla.GetWffPredAndArgs(goal)

			switch pc {
			case fmla.Top, fmla.Equals:
				// Do nothing. These are 0-justification introduction rules.
			case fmla.Bot:
				lns = prf.GetLegalLines()

				for _, ln = range lns {
					if li = ln.GetLineInfo(); li.Mop == fmla.Neg {
						ipWff, _ = fmla.GetWffSubformulae(li.Wff)

						goals = append(goals, ipWff)
					}

					ipWff = fmla.NewCompositeWff(fmla.Neg, li.Wff, nil, 0, 0)

					goals = append(goals, ipWff)
				}
			default:
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
			pcs, acs = prf.SelectNonArbConsts()

			switch {
			case pv != 0:
				for _, pc = range pcs {
					ipWff = fmla.Instantiate(goal, pc, 0)

					goals = append(goals, ipWff)
				}
			case av != 0:
				for _, ac = range acs {
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

				ipGoal = fmla.Instantiate(goal, apc, 0)

				added += prf.AddUniqueInnerProof(ipWff, ipGoal, pr.ForAllIntro)
			case av != 0:
				ipWff = fmla.NewAtomicWff(fmla.Top)

				_, aac = prf.MustSelectArbConsts()

				ipGoal = fmla.Instantiate(goal, 0, aac)

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
	added += helpSeedInnerIntroProofs(prf)

	return
}

func helpSeedInnerElimProofs(prf *pr.Proof) (added uint) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
	)

	prfsI = collectInnerProofs(prf)

	for _, prfI = range prfsI {
		added += seedInnerElimProofs(prfI) + helpSeedInnerElimProofs(prfI)
	}

	return
}

func seedInnerElimProofs(prf *pr.Proof) (added uint) {
	var (
		lns        []*pr.Line
		ln         *pr.Line
		li         *pr.LineInfo
		apc        fmla.Predicate
		aac        fmla.Argument
		goals      []*fmla.WffTree
		goal, wffG *fmla.WffTree
		ok         bool
	)

	lns = prf.GetLocalLines()

	for _, ln = range lns {
		li = ln.GetLineInfo()

		switch li.Mop {
		case fmla.NoSymbol, fmla.Neg, fmla.Wedge,
			fmla.Iff, fmla.ForAll, fmla.Box:
			// If a line doesn't have these (or any) symbols, there's nothing to do.
		case fmla.Vee:
			goals = prf.PopMetSubgoals()

			ok = false

			for _, goal = range goals {
				wffG = fmla.NewCompositeWff(fmla.To, li.SubL, goal, 0, 0)

				ok = ok || prf.ExtendSubgoals(wffG)

				wffG = fmla.NewCompositeWff(fmla.To, li.SubR, goal, 0, 0)

				ok = ok || prf.ExtendSubgoals(wffG)
			}

			if ok {
				added += seedInnerIntroProofs(prf)
			}
		case fmla.To:
			wffG = fmla.NewCompositeWff(fmla.Neg, li.SubL, nil, 0, 0)

			if ok = prf.ExtendSubgoals(li.SubL, wffG); ok {
				added += seedInnerIntroProofs(prf)
			}
		case fmla.Exists:
			apc, aac = prf.MustSelectArbConsts()

			switch {
			case li.PVar != 0 && apc != 0:
				wffG = fmla.Instantiate(li.SubL, apc, 0)

				goal = fmla.NewAtomicWff(fmla.Top)

				added += prf.AddUniqueInnerProof(wffG, goal, pr.ExistsElim, ln)
			case li.AVar != 0 && aac != 0:
				wffG = fmla.Instantiate(li.SubL, 0, aac)

				goal = fmla.NewAtomicWff(fmla.Top)

				added += prf.AddUniqueInnerProof(wffG, goal, pr.ExistsElim, ln)
			default:
				panic("Invalid WffTree, or missing arbitrary constant.")
			}
		case fmla.Diamond:
			goal = fmla.NewAtomicWff(fmla.Top)

			added += prf.AddUniqueInnerProof(li.SubL, goal, pr.DiamondElim, ln)
		default:
			panic("Invalid WffTree")
		}
	}

	// Traverse the inner proofs, themselves, for further inner proofs
	// to those inner proofs' goals.
	added += helpSeedInnerElimProofs(prf)

	return
}
