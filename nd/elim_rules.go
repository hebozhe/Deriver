package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
)

var tryToElim ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		lns      []*pr.Line
		j1, j2   *pr.Line
		j1i, j2i *pr.LineInfo
		got2     bool
	)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		if j1i = j1.GetLineInfo(); j1i.Mop != fmla.To {
			continue
		}

		got2 = false

		for _, j2 = range lns {
			if j2i = j2.GetLineInfo(); fmla.IsIdentical(j2i.Wff, j1i.SubL) {
				got2 = true

				break
			}
		}

		switch got2 {
		case true:
			added += prf.MustAddNewLine(j1i.SubR, pr.ToElim, j1, j2)
		case false:
			_ = prf.ExtendSubgoals(j1i.SubL)
		}
	}

	return
}

var tryWedgeElim ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		lns []*pr.Line
		j1  *pr.Line
		j1i *pr.LineInfo
	)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		if j1i = j1.GetLineInfo(); j1i.Mop != fmla.Wedge {
			continue
		}

		added += prf.MustAddNewLine(j1i.SubL, pr.WedgeElim, j1)
		added += prf.MustAddNewLine(j1i.SubR, pr.WedgeElim, j1)
	}

	return
}

var tryVeeElim ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		lns           []*pr.Line
		j1, j2, j3    *pr.Line
		j1i, j2i, j3i *pr.LineInfo
		got2, got3    bool
		wffD, goal    *fmla.WffTree
	)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		if j1i = j1.GetLineInfo(); j1i.Mop != fmla.Vee {
			continue
		}

		for _, j2 = range lns {
			if j2i = j2.GetLineInfo(); j2i.Mop == fmla.To && fmla.IsIdentical(j2i.SubL, j1i.SubL) {
				got2 = true

				break
			}
		}

		for _, j3 = range lns {
			if j3i = j3.GetLineInfo(); j3i.Mop == fmla.To && fmla.IsIdentical(j3i.SubL, j1i.SubR) {
				got3 = true

				break
			}
		}

		switch {
		case got2 && got3 && fmla.IsIdentical(j2i.SubR, j3i.SubR):
			added += prf.MustAddNewLine(j2i.SubR, pr.VeeElim, j1, j2, j3)
		case got2 && got3:
			wffD = fmla.NewCompositeWff(fmla.Vee, j2i.SubR, j3i.SubR, 0, 0)
			wffD = fmla.NewCompositeWff(fmla.To, j1i.SubL, wffD, 0, 0)

			_ = prf.ExtendSubgoals(wffD)

			wffD = fmla.NewCompositeWff(fmla.Vee, j2i.SubR, j3i.SubR, 0, 0)
			wffD = fmla.NewCompositeWff(fmla.To, j1i.SubR, wffD, 0, 0)

			_ = prf.ExtendSubgoals(wffD)
		// There's probably more to exploit, but I'm a lazy bitch.
		// Motherfucking DS rules for MPL vs. IPL...
		// Disjunction contraction when j1i.SubL == j1i.SubR...
		default:
			for _, goal = range prf.GetAllGoals() {
				wffD = fmla.NewCompositeWff(fmla.To, j1i.SubL, goal, 0, 0)

				_ = prf.ExtendSubgoals(wffD)

				wffD = fmla.NewCompositeWff(fmla.To, j1i.SubR, goal, 0, 0)

				_ = prf.ExtendSubgoals(wffD)
			}
		}
	}

	return
}

var tryIffElim ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		lns  []*pr.Line
		j1   *pr.Line
		j1i  *pr.LineInfo
		wffD *fmla.WffTree
	)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		if j1i = j1.GetLineInfo(); j1i.Mop != fmla.Iff {
			continue
		}

		wffD = fmla.NewCompositeWff(fmla.To, j1i.SubL, j1i.SubR, 0, 0)

		_ = prf.ExtendSubgoals(wffD)

		wffD = fmla.NewCompositeWff(fmla.To, j1i.SubR, j1i.SubL, 0, 0)

		_ = prf.ExtendSubgoals(wffD)
	}

	return
}

var tryBotElim ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		Fwff, wffD *fmla.WffTree
		goals      []*fmla.WffTree
		lns        []*pr.Line
		j1         *pr.Line
		j1i        *pr.LineInfo
	)

	Fwff = fmla.NewAtomicWff(fmla.Bot)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		if j1i = j1.GetLineInfo(); !fmla.IsIdentical(j1i.Wff, Fwff) {
			continue
		}

		goals = prf.GetAllGoals()

		for _, wffD = range goals {
			added += prf.MustAddNewLine(wffD, pr.BotElim, j1)
		}

		break
	}

	return
}

var tryNegElim ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		lns  []*pr.Line
		j1   *pr.Line
		j1i  *pr.LineInfo
		mop  fmla.Symbol
		wffD *fmla.WffTree
	)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		if j1i = j1.GetLineInfo(); j1i.Mop != fmla.Neg {
			continue
		}

		if mop = fmla.GetWffMop(j1i.SubL); mop != fmla.Neg {
			continue
		}

		wffD, _ = fmla.GetWffSubformulae(j1i.SubL)

		added += prf.MustAddNewLine(wffD, pr.NegElim, j1)
	}

	return
}

var tryForAllElim ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		lns  []*pr.Line
		j1   *pr.Line
		j1i  *pr.LineInfo
		wffD *fmla.WffTree
		pcs  []fmla.Predicate
		acs  []fmla.Argument
		pc   fmla.Predicate
		ac   fmla.Argument
	)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		if j1i = j1.GetLineInfo(); j1i.Mop != fmla.ForAll {
			continue
		}

		pcs, acs = prf.MustSelectHadConsts()

		switch {
		case j1i.PVar != 0:
			for _, pc = range pcs {
				wffD = fmla.ReplacePreds(j1i.SubL, j1i.PVar, pc)

				added += prf.MustAddNewLine(wffD, pr.ForAllElim, j1)
			}
		case j1i.AVar != 0:
			for _, ac = range acs {
				wffD = fmla.ReplaceArgs(j1i.SubL, j1i.AVar, ac)

				added += prf.MustAddNewLine(wffD, pr.ForAllElim, j1)
			}
		}

	}

	return
}

var tryExistsElim ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		prfsI      []*pr.Proof
		prfI       *pr.Proof
		j1, j2, j3 *pr.Line
		met        bool
		j2i, j3i   *pr.LineInfo
	)

	prfsI = prf.GetInnerProofs(pr.ExistsElim)

	for _, prfI = range prfsI {
		if j2, j3, met = prfI.HeadGoalMet(); !met {
			continue
		}

		j2i, j3i = j2.GetLineInfo(), j3.GetLineInfo()

		j1 = j2i.J1

		added += prf.MustAddNewLine(j3i.Wff, pr.ExistsElim, j1, j2, j3)
	}

	return
}

var tryBoxElim ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		purp   pr.NDRule
		lns    []*pr.Line
		j1, j2 *pr.Line
		j1i    *pr.LineInfo
	)

	if j2, purp = prf.GetFirstLineAndPurpose(); purp == pr.BoxIntro || purp == pr.DiamondElim {
		lns = prf.GetLegalLines()

		for _, j1 = range lns {
			if j1i = j1.GetLineInfo(); j1i.Mop != fmla.Box {
				continue
			}

			added += prf.MustAddNewLine(j1i.SubL, pr.BotElim, j1, j2)
		}
	}

	return
}

var tryDiamondElim ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		prfsI      []*pr.Proof
		prfI       *pr.Proof
		j1, j2, j3 *pr.Line
		j2i, j3i   *pr.LineInfo
		met        bool
	)

	prfsI = prf.GetInnerProofs(pr.DiamondElim)

	for _, prfI = range prfsI {
		if j2, j3, met = prfI.HeadGoalMet(); !met {
			continue
		}

		j2i, j3i = j2.GetLineInfo(), j3.GetLineInfo()

		j1 = j2i.J1

		added += prf.MustAddNewLine(j3i.Wff, pr.DiamondElim, j1, j2, j3)
	}

	return
}

var tryElimM ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		lns []*pr.Line
		j1  *pr.Line
		j1i *pr.LineInfo
	)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		if j1i = j1.GetLineInfo(); j1i.Mop != fmla.Box {
			continue
		}

		added += prf.MustAddNewLine(j1i.SubL, pr.ElimM, j1)
	}

	return
}

var tryElim4 ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		lns []*pr.Line
		j1  *pr.Line
		mop fmla.Symbol
		j1i *pr.LineInfo
	)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		if j1i = j1.GetLineInfo(); j1i.Mop != fmla.Diamond {
			continue
		}

		if mop = fmla.GetWffMop(j1i.SubL); mop != fmla.Diamond {
			continue
		}

		added += prf.MustAddNewLine(j1i.SubL, pr.Elim4, j1)
	}

	return
}

var tryElimB ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		lns  []*pr.Line
		j1   *pr.Line
		mop  fmla.Symbol
		j1i  *pr.LineInfo
		wffD *fmla.WffTree
	)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		if j1i = j1.GetLineInfo(); j1i.Mop != fmla.Diamond {
			continue
		}

		if mop = fmla.GetWffMop(j1i.SubL); mop != fmla.Box {
			continue
		}

		wffD, _ = fmla.GetWffSubformulae(j1i.SubL)

		added += prf.MustAddNewLine(wffD, pr.ElimB, j1)
	}

	return
}
