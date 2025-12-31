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
	)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		if j1i = j1.GetLineInfo(); j1i.Mop != fmla.To {
			continue
		}

		for _, j2 = range lns {
			if j2i = j2.GetLineInfo(); fmla.IsIdentical(j2i.Wff, j1i.SubL) {
				added += prf.AddUniqueLine(j1i.SubR, pr.ToElim, j1, j2)
			}
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

		added += prf.AddUniqueLine(j1i.SubL, pr.WedgeElim, j1)
		added += prf.AddUniqueLine(j1i.SubR, pr.WedgeElim, j1)
	}

	return
}

var tryVeeElim ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		lns           []*pr.Line
		j1, j2, j3    *pr.Line
		j1i, j2i, j3i *pr.LineInfo
	)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		if j1i = j1.GetLineInfo(); j1i.Mop != fmla.Vee {
			continue
		}

		for _, j2 = range lns {
			if j2i = j2.GetLineInfo(); !(j2i.Mop == fmla.To && fmla.IsIdentical(j2i.SubL, j1i.SubL)) {
				continue
			}

			for _, j3 = range lns {
				if j3i = j3.GetLineInfo(); !(j3i.Mop == fmla.To && fmla.IsIdentical(j3i.SubL, j1i.SubR)) {
					continue
				}

				if fmla.IsIdentical(j2i.SubR, j3i.SubR) {
					added += prf.AddUniqueLine(j2i.SubR, pr.VeeElim, j1, j2, j3)
				}
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

		added += prf.AddUniqueLine(wffD, pr.IffElim, j1)

		wffD = fmla.NewCompositeWff(fmla.To, j1i.SubR, j1i.SubL, 0, 0)

		added += prf.AddUniqueLine(wffD, pr.IffElim, j1)
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
			added += prf.AddUniqueLine(wffD, pr.BotElim, j1)
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

		added += prf.AddUniqueLine(wffD, pr.NegElim, j1)
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

		pcs, acs = prf.SelectNonArbConsts()

		switch {
		case j1i.PVar != 0:
			for _, pc = range pcs {
				wffD = fmla.ReplacePreds(j1i.SubL, j1i.PVar, pc)

				added += prf.AddUniqueLine(wffD, pr.ForAllElim, j1)
			}
		case j1i.AVar != 0:
			for _, ac = range acs {
				wffD = fmla.ReplaceArgs(j1i.SubL, j1i.AVar, ac)

				added += prf.AddUniqueLine(wffD, pr.ForAllElim, j1)
			}
		}
	}

	return
}

var tryExistsElim ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		prfsI      []*pr.Proof
		prfI       *pr.Proof
		lnsI       []*pr.Line
		j1, j2, j3 *pr.Line
		j2i, j3i   *pr.LineInfo
		apc        fmla.Predicate
		aac        fmla.Argument
	)

	prfsI = prf.GetInnerProofs(pr.ExistsElim)

	for _, prfI = range prfsI {
		apc, aac = prfI.GetArbConstsFromProof()

		lnsI = prfI.GetLocalLines()

		j2 = lnsI[0]

		j2i = j2.GetLineInfo()

		j1 = j2i.J1

		for _, j3 = range lnsI[1:] {
			if j3i = j3.GetLineInfo(); fmla.HasPred(j3i.Wff, apc) || fmla.HasArg(j3i.Wff, aac) {
				continue
			}

			added += prf.AddUniqueLine(j3i.Wff, pr.ExistsElim, j1, j2, j3)
		}
	}

	return
}

var tryEqualsElim ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		lns      []*pr.Line
		j1, j2   *pr.Line
		j1i, j2i *pr.LineInfo
		pred     fmla.Predicate
		args     []fmla.Argument
		wffsD    []*fmla.WffTree
		wffD     *fmla.WffTree
	)

	lns = prf.GetLegalLines()

	for _, j1 = range lns {
		if j1i = j1.GetLineInfo(); j1i.Mop != fmla.NoSymbol {
			continue
		}

		if pred, args, _ = fmla.GetWffPredAndArgs(j1i.Wff); pred != fmla.Equals {
			continue
		}

		if args[0] == args[1] {
			continue
		}

		for _, j2 = range lns {
			j2i = j2.GetLineInfo()

			if fmla.HasArg(j2i.Wff, args[0]) {
				wffsD = fmla.ReplaceEachArgOnce(j2i.Wff, args[0], args[1])

				for _, wffD = range wffsD {
					added += prf.AddUniqueLine(wffD, pr.EqualsElim, j1, j2)
				}

			}

			if fmla.HasArg(j2i.Wff, args[1]) {
				wffsD = fmla.ReplaceEachArgOnce(j2i.Wff, args[1], args[0])

				for _, wffD = range wffsD {
					added += prf.AddUniqueLine(wffD, pr.EqualsElim, j1, j2)
				}
			}
		}
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

			added += prf.AddUniqueLine(j1i.SubL, pr.BoxElim, j1, j2)
		}
	}

	return
}

var tryDiamondElim ndRuleFunc = func(prf *pr.Proof) (added uint) {
	var (
		prfsI      []*pr.Proof
		prfI       *pr.Proof
		lnsI       []*pr.Line
		j1, j2, j3 *pr.Line
		j2i, j3i   *pr.LineInfo
		wffD       *fmla.WffTree
	)

	prfsI = prf.GetInnerProofs(pr.DiamondElim)

	for _, prfI = range prfsI {
		lnsI = prfI.GetLocalLines()

		j2 = lnsI[0]

		j2i = j2.GetLineInfo()

		j1 = j2i.J1

		for _, j3 = range lnsI[1:] {
			// Is there even a risk of this?
			if !prfI.LineWorldIsProofWorld(j3) {
				continue
			}

			j3i = j3.GetLineInfo()

			wffD = fmla.NewCompositeWff(fmla.Diamond, j3i.Wff, nil, 0, 0)

			added += prf.AddUniqueLine(wffD, pr.DiamondElim, j1, j2, j3)
		}
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

		added += prf.AddUniqueLine(j1i.SubL, pr.ElimM, j1)
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

		added += prf.AddUniqueLine(j1i.SubL, pr.Elim4, j1)
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

		added += prf.AddUniqueLine(wffD, pr.ElimB, j1)
	}

	return
}
