package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
	"slices"
)

var tryTopIntro ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		wff *fmla.WffTree
	)

	wff = fmla.NewAtomicWff(fmla.Top)

	added += prf.MustAddNewLine(wff, pr.TopIntro)

	return
}

var tryToIntro ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		prfsI    []*pr.Proof
		prfI     *pr.Proof
		j1, j2   *pr.Line
		j1i, j2i *pr.LineInfo
		met      bool
		wffD     *fmla.WffTree
	)

	prfsI = prf.GetInnerProofs(pr.ToIntro)

	for _, prfI = range prfsI {
		if j1, j2, met = prfI.HeadGoalMet(); !met {
			continue
		}

		j1i, j2i = j1.GetLineInfo(), j2.GetLineInfo()

		wffD = fmla.NewCompositeWff(fmla.To, j1i.Wff, j2i.Wff, 0, 0)

		added += prf.MustAddNewLine(wffD, pr.ToIntro, j1, j2)
	}

	return
}

var tryWedgeIntro ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		goals              []*fmla.WffTree
		lns                []*pr.Line
		mop                fmla.Symbol
		wffD, wffDL, wffDR *fmla.WffTree
		j1, j2             *pr.Line
		j1i, j2i           *pr.LineInfo
		got1, got2         bool
	)

	goals = prf.GetAllGoals()

	lns = prf.GetLegalLines()

	for _, wffD = range goals {
		if mop = fmla.GetWffMop(wffD); mop != fmla.Wedge {
			continue
		}

		wffDL, wffDR = fmla.GetWffSubformulae(wffD)

		for _, j1 = range lns {
			if j1i = j1.GetLineInfo(); fmla.IsIdentical(j1i.Wff, wffDL) {
				got1 = true

				break
			}
		}

		for _, j2 = range lns {
			if j2i = j2.GetLineInfo(); fmla.IsIdentical(j2i.Wff, wffDR) {
				got2 = true

				break
			}
		}

		switch {
		case got1 && got2:
			added += prf.MustAddNewLine(wffD, pr.WedgeIntro, j1, j2)
		case got1:
			_ = prf.ExtendSubgoals(wffDR)
		case got2:
			_ = prf.ExtendSubgoals(wffDL)
		default:
			_ = prf.ExtendSubgoals(wffDL, wffDR)
		}
	}

	return
}

var tryVeeIntro ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		goals              []*fmla.WffTree
		lns                []*pr.Line
		mop                fmla.Symbol
		wffD, wffDL, wffDR *fmla.WffTree
		j1                 *pr.Line
		j1i                *pr.LineInfo
	)

	goals = prf.GetAllGoals()

	lns = prf.GetLegalLines()

	for _, wffD = range goals {
		if mop = fmla.GetWffMop(wffD); mop != fmla.Vee {
			continue
		}

		wffDL, wffDR = fmla.GetWffSubformulae(wffD)

		for _, j1 = range lns {
			if j1i = j1.GetLineInfo(); fmla.IsIdentical(j1i.Wff, wffDL) || fmla.IsIdentical(j1i.Wff, wffDR) {
				added += prf.MustAddNewLine(wffD, pr.VeeIntro, j1)
			}
		}
	}

	return
}

var tryIffIntro ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		goals              []*fmla.WffTree
		lns                []*pr.Line
		mop                fmla.Symbol
		wffD, wffDL, wffDR *fmla.WffTree
		j1, j2             *pr.Line
		j1i, j2i           *pr.LineInfo
		got1, got2         bool
	)

	goals = prf.GetAllGoals()

	lns = prf.GetLegalLines()

	for _, wffD = range goals {
		if mop = fmla.GetWffMop(wffD); mop != fmla.Iff {
			continue
		}

		wffDL, wffDR = fmla.GetWffSubformulae(wffD)

		got1, got2 = false, false

		for _, j1 = range lns {
			if j1i = j1.GetLineInfo(); j1i.Mop == fmla.To &&
				fmla.IsIdentical(j1i.SubL, wffDL) &&
				fmla.IsIdentical(j1i.SubR, wffDR) {
				got1 = true

				break
			}
		}

		for _, j2 = range lns {
			if j2i = j2.GetLineInfo(); j2i.Mop == fmla.To &&
				fmla.IsIdentical(j2i.SubL, wffDR) &&
				fmla.IsIdentical(j2i.SubR, wffDL) {
				got2 = true

				break
			}
		}

		switch {
		case got1 && got2:
			added += prf.MustAddNewLine(wffD, pr.IffIntro, j1, j2)
		case got1:
			wffD = fmla.NewCompositeWff(fmla.To, wffDR, wffDL, 0, 0)

			_ = prf.ExtendSubgoals(wffD)
		case got2:
			wffD = fmla.NewCompositeWff(fmla.To, wffDL, wffDR, 0, 0)

			_ = prf.ExtendSubgoals(wffD)
		default:
			wffD = fmla.NewCompositeWff(fmla.To, wffDR, wffDL, 0, 0)

			_ = prf.ExtendSubgoals(wffD)

			wffD = fmla.NewCompositeWff(fmla.To, wffDL, wffDR, 0, 0)

			_ = prf.ExtendSubgoals(wffD)
		}
	}

	return
}

var tryReit ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		legs, locs []*pr.Line
		j1         *pr.Line
		j1i        *pr.LineInfo
		contains   func(ln *pr.Line) (has bool)
	)

	legs, locs = prf.GetLegalLines(), prf.GetLocalLines()

	contains = func(ln *pr.Line) (has bool) {
		var li *pr.LineInfo = ln.GetLineInfo()

		has = fmla.IsIdentical(li.Wff, j1i.Wff)

		return
	}

	for _, j1 = range legs {
		if j1i = j1.GetLineInfo(); slices.ContainsFunc(locs, contains) {
			continue
		}

		added += prf.MustAddNewLine(j1i.Wff, pr.Reit, j1)
	}

	return
}

var tryBotIntro ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		lns      []*pr.Line
		j1, j2   *pr.Line
		dex      int
		j1i, j2i *pr.LineInfo
		wffD     *fmla.WffTree
	)

	lns = prf.GetLegalLines()

TRYBOTINTRO_OUTER:
	for dex, j1 = range lns {
		j1i = j1.GetLineInfo()

		for _, j2 = range lns[dex+1:] {
			j2i = j2.GetLineInfo()

			if j1i.Mop == fmla.Neg && fmla.IsIdentical(j1i.SubL, j2i.Wff) {
				wffD = fmla.NewAtomicWff(fmla.Bot)

				added += prf.MustAddNewLine(wffD, pr.BotIntro, j1, j2)

				break TRYBOTINTRO_OUTER
			}

			if j2i.Mop == fmla.Neg && fmla.IsIdentical(j2i.SubL, j1i.Wff) {
				wffD = fmla.NewAtomicWff(fmla.Bot)

				added += prf.MustAddNewLine(wffD, pr.BotIntro, j2, j1)

				break TRYBOTINTRO_OUTER
			}
		}
	}

	if added == 0 {
		for _, j1 = range lns {
			j1i = j1.GetLineInfo()

			wffD = fmla.NewCompositeWff(fmla.Neg, j1i.Wff, nil, 0, 0)

			_ = prf.ExtendSubgoals(wffD)
		}
	}

	return
}

var tryNegIntro ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		prfsI  []*pr.Proof
		prfI   *pr.Proof
		j1, j2 *pr.Line
		j1i    *pr.LineInfo
		met    bool
		wffD   *fmla.WffTree
	)

	prfsI = prf.GetInnerProofs(pr.NegIntro)

	for _, prfI = range prfsI {
		if j1, j2, met = prfI.HeadGoalMet(); !met {
			continue
		}

		j1i = j1.GetLineInfo()

		wffD = fmla.NewCompositeWff(fmla.Neg, j1i.Wff, nil, 0, 0)

		added += prf.MustAddNewLine(wffD, pr.NegIntro, j1, j2)
	}

	return
}

var tryForAllIntro ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		prfsI   []*pr.Proof
		prfI    *pr.Proof
		j1, j2  *pr.Line
		j2i     *pr.LineInfo
		met     bool
		apc, pv fmla.Predicate
		aac, av fmla.Argument
		wffD    *fmla.WffTree
	)

	prfsI = prf.GetInnerProofs(pr.ForAllIntro)

	for _, prfI = range prfsI {
		if j1, j2, met = prfI.HeadGoalMet(); !met {
			continue
		}

		j2i = j2.GetLineInfo()

		apc, aac = prf.GetArbConsts()

		switch {
		case apc != 0:
			for _, pv = range fmla.PredVars {
				wffD = fmla.GeneralizePred(fmla.ForAll, j2i.Wff, apc, pv)

				if prf.MeetsAnyGoal(wffD) {
					added += prf.MustAddNewLine(wffD, pr.ForAllIntro, j1, j2)
				}
			}

		case aac != 0:
			for _, av = range fmla.ArgVars {
				wffD = fmla.GeneralizeArg(fmla.ForAll, j2i.Wff, aac, av)

				if prf.MeetsAnyGoal(wffD) {
					added += prf.MustAddNewLine(wffD, pr.ForAllIntro, j1, j2)
				}
			}
		}
	}

	return
}

var tryExistsIntro ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		goals      []*fmla.WffTree
		wffD, wffI *fmla.WffTree
		lns        []*pr.Line
		mop        fmla.Symbol
		j1         *pr.Line
		j1i        *pr.LineInfo
		pcs        []fmla.Predicate
		acs        []fmla.Argument
		pv, pc     fmla.Predicate
		av, ac     fmla.Argument
	)

	goals = prf.GetAllGoals()

	lns = prf.GetLegalLines()

TRYEXISTSINTRO_OUTER:
	for _, wffD = range goals {
		if mop, pv, av = fmla.GetWffMopAndVars(wffD); mop != fmla.Exists {
			continue
		}

		pcs, acs = prf.MustSelectHadConsts()

		switch {
		case pv != 0:
			for _, pc = range pcs {
				wffI = fmla.Instantiate(wffD, pc, 0)

				for _, j1 = range lns {
					if j1i = j1.GetLineInfo(); !fmla.IsIdentical(j1i.Wff, wffI) {
						continue
					}

					added += prf.MustAddNewLine(wffD, pr.ExistsIntro, j1)

					continue TRYEXISTSINTRO_OUTER
				}
			}

		case av != 0:
			for _, ac = range acs {
				wffI = fmla.Instantiate(wffD, 0, ac)

				for _, j1 = range lns {
					if j1i = j1.GetLineInfo(); !fmla.IsIdentical(j1i.Wff, wffI) {
						continue
					}

					added += prf.MustAddNewLine(wffD, pr.ExistsIntro, j1)

					continue TRYEXISTSINTRO_OUTER
				}
			}
		}
	}

	return
}

var tryBoxIntro ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		prfsI  []*pr.Proof
		prfI   *pr.Proof
		j1, j2 *pr.Line
		j2i    *pr.LineInfo
		met    bool
		wffD   *fmla.WffTree
	)

	prfsI = prf.GetInnerProofs(pr.BoxIntro)

	for _, prfI = range prfsI {
		if j1, j2, met = prfI.HeadGoalMet(); !met {
			continue
		}

		j2i = j2.GetLineInfo()

		wffD = fmla.NewCompositeWff(fmla.Box, j2i.Wff, nil, 0, 0)

		added += prf.MustAddNewLine(wffD, pr.BoxIntro, j1, j2)
	}

	return
}

var tryDiamondIntro ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		lns         []*pr.Line
		j1          *pr.Line
		j1i         *pr.LineInfo
		mop         fmla.Symbol
		wffD, wffDL *fmla.WffTree
	)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		if j1i = j1.GetLineInfo(); j1i.Mop != fmla.Neg {
			continue
		}

		if mop = fmla.GetWffMop(j1i.SubL); mop != fmla.Box {
			continue
		}

		wffDL, _ = fmla.GetWffSubformulae(j1i.SubL)

		wffD = fmla.NewUnaryChainWff([]fmla.Symbol{fmla.Diamond, fmla.Neg}, wffDL)

		added += prf.MustAddNewLine(wffD, pr.DiamondIntro, j1)
	}

	return
}

var tryIntroD ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		lns  []*pr.Line
		j1   *pr.Line
		j1i  *pr.LineInfo
		wffD *fmla.WffTree
	)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		if j1i = j1.GetLineInfo(); j1i.Mop != fmla.Box {
			continue
		}

		wffD, _ = fmla.GetWffSubformulae(j1i.SubL)
		wffD = fmla.NewCompositeWff(fmla.Diamond, wffD, nil, 0, 0)

		added += prf.MustAddNewLine(wffD, pr.IntroD, j1)
	}

	return
}

var tryIntroM ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		lns  []*pr.Line
		j1   *pr.Line
		j1i  *pr.LineInfo
		wffD *fmla.WffTree
	)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		j1i = j1.GetLineInfo()

		wffD = fmla.NewCompositeWff(fmla.Diamond, j1i.Wff, nil, 0, 0)

		if prf.MeetsAnyGoal(wffD) {
			added += prf.MustAddNewLine(wffD, pr.IntroM, j1)
		}
	}

	return
}

var tryIntro4 ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		lns  []*pr.Line
		j1   *pr.Line
		j1i  *pr.LineInfo
		wffD *fmla.WffTree
	)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		if j1i = j1.GetLineInfo(); j1i.Mop != fmla.Box {
			continue
		}

		wffD = fmla.NewCompositeWff(fmla.Box, j1i.Wff, nil, 0, 0)

		if prf.MeetsAnyGoal(wffD) {
			added += prf.MustAddNewLine(wffD, pr.Intro4, j1)
		}
	}

	return
}

var tryIntroB ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		lns  []*pr.Line
		j1   *pr.Line
		j1i  *pr.LineInfo
		wffD *fmla.WffTree
	)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		j1i = j1.GetLineInfo()

		wffD = fmla.NewUnaryChainWff([]fmla.Symbol{fmla.Box, fmla.Diamond}, j1i.Wff)

		if prf.MeetsAnyGoal(wffD) {
			added += prf.MustAddNewLine(wffD, pr.IntroB, j1)
		}
	}

	return
}
