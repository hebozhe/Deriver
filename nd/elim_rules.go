package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
)

var tryToElim NDFunc = func(prf *pr.Proof) (prfD *pr.Proof) {
	var (
		lns      []*pr.Line
		j1, j2   *pr.Line
		j1i, j2i *pr.LineInfo
		got2     bool
	)

	lns = pr.GetAdmissibleLines(prf)

	for _, j1 = range lns {
		if j1i = pr.GetLineInfo(j1); j1i.Mop != fmla.To {
			continue
		}

		got2 = false

		for _, j2 = range lns {
			if j2i = pr.GetLineInfo(j2); fmla.IsIdentical(j2i.Wff, j1i.SubL) {
				got2 = true

				break
			}
		}

		switch got2 {
		case true:
			prf = pr.AddLineToProof(prf, j1i.SubR, pr.ToElim, j1, j2)
		case false:
			prf = pr.AddGoalsToProof(prf, j1i.SubL)
		}
	}

	prfD = prf

	return
}

var tryWedgeElim NDFunc = func(prf *pr.Proof) (prfD *pr.Proof) {
	var (
		lns []*pr.Line
		j1  *pr.Line
		j1i *pr.LineInfo
	)

	lns = pr.GetAdmissibleLines(prf)

	for _, j1 = range lns {
		if j1i = pr.GetLineInfo(j1); j1i.Mop != fmla.Wedge {
			continue
		}

		prf = pr.AddLineToProof(prf, j1i.SubL, pr.WedgeElim, j1)
		prf = pr.AddLineToProof(prf, j1i.SubR, pr.WedgeElim, j1)
	}

	prfD = prf

	return
}

func pumpGoalsForVeeElim(prf *pr.Proof, j1i *pr.LineInfo) (prfD *pr.Proof) {
	var (
		pi         *pr.ProofInfo
		goal, wffD *fmla.WffTree
	)

	pi = pr.GetProofInfo(prf)

	for _, goal = range pi.Goals {
		wffD = fmla.NewCompositeWff(fmla.To, j1i.SubL, goal, 0, 0)

		prf = pr.AddGoalsToProof(prf, wffD)

		wffD = fmla.NewCompositeWff(fmla.To, j1i.SubR, goal, 0, 0)

		prf = pr.AddGoalsToProof(prf, wffD)
	}

	wffD = fmla.NewCompositeWff(fmla.To, j1i.SubL, j1i.SubL, 0, 0)

	prf = pr.AddGoalsToProof(prf, wffD)

	wffD = fmla.NewCompositeWff(fmla.To, j1i.SubL, j1i.SubR, 0, 0)

	prf = pr.AddGoalsToProof(prf, wffD)

	wffD = fmla.NewCompositeWff(fmla.To, j1i.SubR, j1i.SubL, 0, 0)

	prf = pr.AddGoalsToProof(prf, wffD)

	wffD = fmla.NewCompositeWff(fmla.To, j1i.SubR, j1i.SubR, 0, 0)

	prf = pr.AddGoalsToProof(prf, wffD)

	prfD = prf

	return
}

var tryVeeElim NDFunc = func(prf *pr.Proof) (prfD *pr.Proof) {
	var (
		lns           []*pr.Line
		j1, j2, j3    *pr.Line
		j1i, j2i, j3i *pr.LineInfo
		got2, got3    bool
	)

	lns = pr.GetAdmissibleLines(prf)

	for _, j1 = range lns {
		if j1i = pr.GetLineInfo(j1); j1i.Mop != fmla.Vee {
			continue
		}

		got2, got3 = false, false

		for _, j2 = range lns {
			if j2i = pr.GetLineInfo(j2); j2i.Mop == fmla.To && fmla.IsIdentical(j2i.SubL, j1i.SubL) {
				got2 = true

				break
			}
		}

		for _, j3 = range lns {
			if j3i = pr.GetLineInfo(j3); j3i.Mop == fmla.To && fmla.IsIdentical(j3i.SubL, j1i.SubR) {
				got3 = true

				break
			}
		}

		switch {
		case got2 && got3 && fmla.IsIdentical(j2i.SubR, j3i.SubR):
			prf = pr.AddLineToProof(prf, j2i.SubR, pr.VeeElim, j1, j2, j3)
		default:
			prf = pumpGoalsForVeeElim(prf, j1i)
		}
	}

	prfD = prf

	return
}

var tryIffElim NDFunc = func(prf *pr.Proof) (prfD *pr.Proof) {
	var (
		lns  []*pr.Line
		j1   *pr.Line
		j1i  *pr.LineInfo
		wffD *fmla.WffTree
	)

	lns = pr.GetAdmissibleLines(prf)

	for _, j1 = range lns {
		if j1i = pr.GetLineInfo(j1); j1i.Mop != fmla.Iff {
			continue
		}

		wffD = fmla.NewCompositeWff(fmla.To, j1i.SubL, j1i.SubR, 0, 0)

		prf = pr.AddGoalsToProof(prf, wffD)

		wffD = fmla.NewCompositeWff(fmla.To, j1i.SubR, j1i.SubL, 0, 0)

		prf = pr.AddGoalsToProof(prf, wffD)
	}

	prfD = prf

	return
}

var tryBotElim NDFunc = func(prf *pr.Proof) (prfD *pr.Proof) {
	var (
		pi         *pr.ProofInfo
		lns        []*pr.Line
		Fwff, wffD *fmla.WffTree
		j1         *pr.Line
		j1i        *pr.LineInfo
	)

	pi = pr.GetProofInfo(prf)

	lns = pr.GetAdmissibleLines(prf)

	Fwff = fmla.NewAtomicWff(fmla.Bot)

	for _, j1 = range lns {
		if j1i = pr.GetLineInfo(j1); !fmla.IsIdentical(j1i.Wff, Fwff) {
			continue
		}

		wffD = pi.Goals[0]

		prf = pr.AddLineToProof(prf, wffD, pr.BotElim, j1)

		break
	}

	prfD = prf

	return
}
