package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
	"slices"
)

var tryTopIntro NDFunc = func(prf *pr.Proof) (prfD *pr.Proof) {
	var (
		wffD *fmla.WffTree
	)

	wffD = fmla.NewAtomicWff(fmla.Top)

	prf = pr.AddLineToProof(prf, wffD, pr.TopIntro)

	prfD = prf

	return
}

var tryToIntro NDFunc = func(prf *pr.Proof) (prfD *pr.Proof) {
	var (
		pi, ipi  *pr.ProofInfo
		prfI     *pr.Proof
		j1, j2   *pr.Line
		j1i, j2i *pr.LineInfo
		got2     bool
		wffD     *fmla.WffTree
	)

	pi = pr.GetProofInfo(prf)

	for _, prfI = range pi.Inner {
		if ipi = pr.GetProofInfo(prfI); ipi.Purp != pr.ToIntro {
			continue
		}

		j1 = ipi.Lns[0]

		got2 = false

		for _, j2 = range ipi.Lns {
			if j2i = pr.GetLineInfo(j2); fmla.IsIdentical(j2i.Wff, ipi.Goals[0]) {
				got2 = true

				break
			}
		}

		switch got2 {
		case true:
			j1i = pr.GetLineInfo(j1)

			wffD = fmla.NewCompositeWff(fmla.To, j1i.SubL, j2i.Wff, 0, 0)

			prf = pr.AddLineToProof(prf, wffD, pr.ToIntro, j1, j2)
		case false:
			// Do nothing... until a strategy arises that would make sense here.
		}
	}

	prfD = prf

	return
}

var tryWedgeIntro NDFunc = func(prf *pr.Proof) (prfD *pr.Proof) {
	var (
		pi                 *pr.ProofInfo
		lns                []*pr.Line
		wffD, wffDL, wffDR *fmla.WffTree
		mop                fmla.Symbol
		j1, j2             *pr.Line
		j1i, j2i           *pr.LineInfo
		got1, got2         bool
	)

	pi = pr.GetProofInfo(prf)

	lns = pr.GetAdmissibleLines(prf)

	for _, wffD = range pi.Goals {
		if mop = fmla.GetWffMainOperator(wffD); mop != fmla.Wedge {
			continue
		}

		wffDL, wffDR = fmla.GetWffSubformulae(wffD)

		got1, got2 = false, false

		for _, j1 = range lns {
			if j1i = pr.GetLineInfo(j1); fmla.IsIdentical(j1i.Wff, wffDL) {
				got1 = true

				break
			}
		}

		for _, j2 = range lns {
			if j2i = pr.GetLineInfo(j2); fmla.IsIdentical(j2i.Wff, wffDR) {
				got2 = true

				break
			}
		}

		switch {
		case got1 && got2:
			prf = pr.AddLineToProof(prf, wffD, pr.WedgeIntro, j1, j2)
		case got1 && !got2:
			prf = pr.AddGoalsToProof(prf, wffDR)
		case !got1 && got2:
			prf = pr.AddGoalsToProof(prf, wffDL)
		case !got1 && !got2:
			prf = pr.AddGoalsToProof(prf, wffDL, wffDR)
		}
	}

	prfD = prf

	return
}

var tryVeeIntro NDFunc = func(prf *pr.Proof) (prfD *pr.Proof) {
	var (
		pi                 *pr.ProofInfo
		wffD, wffDL, wffDR *fmla.WffTree
		j1                 *pr.Line
		j1i                *pr.LineInfo
		got1               bool
	)

	pi = pr.GetProofInfo(prf)

	for _, wffD = range pi.Goals {
		if fmla.GetWffMainOperator(wffD) != fmla.Vee {
			continue
		}

		wffDL, wffDR = fmla.GetWffSubformulae(wffD)

		for _, j1 = range pi.Lns {
			if j1i = pr.GetLineInfo(j1); fmla.IsIdentical(j1i.Wff, wffDL) || fmla.IsIdentical(j1i.Wff, wffDR) {
				got1 = true

				break
			}
		}

		switch got1 {
		case true:
			prf = pr.AddLineToProof(prf, wffD, pr.VeeIntro, j1)
		case false:
			prf = pr.AddGoalsToProof(prf, wffDL, wffDR)

			// In CPL, a double-negated disjunction is an acceptable goal.
			wffD = fmla.NewCompositeWff(fmla.Neg, wffD, nil, 0, 0)
			wffD = fmla.NewCompositeWff(fmla.Neg, wffD, nil, 0, 0)

			prf = pr.AddGoalsToProof(prf, wffD)
		}
	}

	prfD = prf

	return
}

var tryIffIntro NDFunc = func(prf *pr.Proof) (prfD *pr.Proof) {
	var (
		pi                 *pr.ProofInfo
		lns                []*pr.Line
		wffD, wffDL, wffDR *fmla.WffTree
		j1, j2             *pr.Line
		j1i, j2i           *pr.LineInfo
		got1, got2         bool
	)

	pi = pr.GetProofInfo(prf)

	lns = pr.GetAdmissibleLines(prf)

	for _, wffD = range pi.Goals {
		if fmla.GetWffMainOperator(wffD) != fmla.Iff {
			continue
		}

		wffDL, wffDR = fmla.GetWffSubformulae(wffD)

		got1, got2 = false, false

		for _, j1 = range lns {
			if j1i = pr.GetLineInfo(j1); j1i.Mop == fmla.To &&
				fmla.IsIdentical(j1i.SubL, wffDL) &&
				fmla.IsIdentical(j1i.SubR, wffDR) {

				got1 = true

				break
			}
		}

		for _, j2 = range lns {
			if j2i = pr.GetLineInfo(j2); j2i.Mop == fmla.To &&
				fmla.IsIdentical(j2i.SubL, wffDR) &&
				fmla.IsIdentical(j2i.SubR, wffDL) {

				got2 = true

				break
			}
		}

		switch {
		case got1 && got2:
			prf = pr.AddLineToProof(prf, wffD, pr.IffIntro, j1, j2)
		case got1 && !got2:
			wffD = fmla.NewCompositeWff(fmla.To, wffDR, wffDL, 0, 0)

			prf = pr.AddGoalsToProof(prf, wffD)
		case !got1 && got2:
			wffD = fmla.NewCompositeWff(fmla.To, wffDL, wffDR, 0, 0)

			prf = pr.AddGoalsToProof(prf, wffD)
		case !got1 && !got2:
			wffD = fmla.NewCompositeWff(fmla.To, wffDR, wffDL, 0, 0)

			prf = pr.AddGoalsToProof(prf, wffD)

			wffD = fmla.NewCompositeWff(fmla.To, wffDL, wffDR, 0, 0)

			prf = pr.AddGoalsToProof(prf, wffD)
		}
	}

	prfD = prf

	return
}

var tryReit NDFunc = func(prf *pr.Proof) (prfD *pr.Proof) {
	var (
		pi  *pr.ProofInfo
		lns []*pr.Line
		j1  *pr.Line
		j1i *pr.LineInfo
	)

	pi = pr.GetProofInfo(prf)

	lns = pr.GetAdmissibleLines(prf)

	for _, j1 = range lns {
		if slices.Contains(pi.Lns, j1) {
			continue
		}

		j1i = pr.GetLineInfo(j1)

		prf = pr.AddLineToProof(prf, j1i.Wff, pr.Reit, j1)
	}

	prfD = prf

	return
}

var tryBotIntro NDFunc = func(prf *pr.Proof) (prfD *pr.Proof) {
	var (
		lns      []*pr.Line
		j1, j2   *pr.Line
		j1i, j2i *pr.LineInfo
		got2     bool
		wffD     *fmla.WffTree
	)

	lns = pr.GetAdmissibleLines(prf)

	for _, j1 = range lns {
		j1i = pr.GetLineInfo(j1)

		for _, j2 = range lns {
			if j2i = pr.GetLineInfo(j2); j2i.Mop == fmla.Neg && fmla.IsIdentical(j2i.SubL, j1i.Wff) {
				got2 = true

				break
			}
		}

		switch got2 {
		case true:
			wffD = fmla.NewAtomicWff(fmla.Bot)

			prf = pr.AddLineToProof(prf, wffD, pr.BotIntro, j1, j2)
		case false:
			wffD = fmla.NewCompositeWff(fmla.Neg, j1i.Wff, nil, 0, 0)

			prf = pr.AddGoalsToProof(prf, wffD)

			if j1i.Mop == fmla.Neg {
				prf = pr.AddGoalsToProof(prf, j1i.SubL)
			}
		}
	}

	prfD = prf

	return
}
