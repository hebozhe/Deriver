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

	_ = prf.MustAddNewLine(wff, pr.TopIntro)

	added = 1

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
		if j1, j2, met = prfI.IntroGoalMet(); !met {
			continue
		}

		j1i, j2i = j1.GetLineInfo(), j2.GetLineInfo()

		wffD = fmla.NewCompositeWff(fmla.To, j1i.Wff, j2i.Wff, 0, 0)

		_ = prf.MustAddNewLine(wffD, pr.ToIntro, j1, j2)

		added += 1
	}

	return
}

var tryWedgeIntro ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		lns      []*pr.Line
		j1, j2   *pr.Line
		j1i, j2i *pr.LineInfo
		wffD     *fmla.WffTree
	)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		j1i = j1.GetLineInfo()

		for _, j2 = range lns {
			j2i = j2.GetLineInfo()

			wffD = fmla.NewCompositeWff(fmla.Wedge, j1i.Wff, j2i.Wff, 0, 0)

			if prf.MeetsGoal(wffD) {
				_ = prf.MustAddNewLine(wffD, pr.WedgeIntro, j1, j2)

				added += 1
			}
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
				_ = prf.MustAddNewLine(wffD, pr.VeeIntro, j1)

				added += 1
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
			_ = prf.MustAddNewLine(wffD, pr.IffIntro, j1, j2)

			added += 1
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
	)

	legs, locs = prf.GetLegalLines(), prf.GetLocalLines()

	for _, j1 = range legs {
		if slices.Contains(locs, j1) {
			continue
		}

		j1i = j1.GetLineInfo()

		_ = prf.MustAddNewLine(j1i.Wff, pr.Reit, j1)

		added += 1
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

				_ = prf.MustAddNewLine(wffD, pr.BotIntro, j1, j2)

				added += 1

				break TRYBOTINTRO_OUTER
			}

			if j2i.Mop == fmla.Neg && fmla.IsIdentical(j2i.SubL, j1i.Wff) {
				wffD = fmla.NewAtomicWff(fmla.Bot)

				_ = prf.MustAddNewLine(wffD, pr.BotIntro, j2, j1)

				added += 1

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
		if j1, j2, met = prfI.IntroGoalMet(); !met {
			continue
		}

		j1i = j1.GetLineInfo()

		wffD = fmla.NewCompositeWff(fmla.Neg, j1i.Wff, nil, 0, 0)

		_ = prf.MustAddNewLine(wffD, pr.NegIntro, j1, j2)

		added += 1
	}

	return
}
