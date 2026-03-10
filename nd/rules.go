package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
)

type ndRuleFunc func(_ *Derivation) (tot int)

// Rules of Implicational Propositional Logic (TPL)

var topIntroFunc ndRuleFunc = func(_ *Derivation) (tot int) {

	return
}

var toIntroFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI    []*pr.Proof
		prfI     *pr.Proof
		purp     pr.NDRule
		is       bool
		ji1, ji2 *pr.LineInfo
		wff      *fmla.WffTree
		ln       *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)

	for _, prfI = range prfsI {
		if purp = prfI.GetPurpose(); purp != pr.ToIntro {
			continue
		}

		if ji2, is = prfI.IsWffGMet(); !is {
			continue
		}

		ji1 = prfI.GetFirstLine()

		wff = fmla.NewCompositeWff(fmla.To, ji1.Wff, ji2.Wff, 0, 0)

		ln, _ = pr.NewLine(wff, nil, pr.ToIntro, 0, nil, ji1.Ln, ji2.Ln)

		tot += ji2.PrfO.InsertLine(ln)

		_ = prfI.CloseProof()
	}

	return
}

var toElimFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI    []*pr.Proof
		prfI     *pr.Proof
		lis      []*pr.LineInfo
		ji1, ji2 *pr.LineInfo
		ln       *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		lis, _ = prfI.GetLegalLines()

		for _, ji1 = range lis {
			if ji1.Mop != fmla.To {
				continue
			}

			for _, ji2 = range lis {
				if !fmla.IsIdentical(ji2.Wff, ji1.SubL) {
					continue
				}

				ln, _ = pr.NewLine(ji1.SubR, nil, pr.ToElim, 0, nil, ji1.Ln, ji2.Ln)

				tot += prfI.InsertLine(ln)
			}
		}
	}

	return
}

var reiterationFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
		purp  pr.NDRule
		lis   []*pr.LineInfo
		li    *pr.LineInfo
		ln    *pr.Line
		wff   *fmla.WffTree
	)

	prfsI = drv.Prf.GetInnerProofs(true)

	for _, prfI = range prfsI {
		if purp = prfI.GetPurpose(); purp == pr.BoxIntro || purp == pr.DiamondElim {
			continue
		}

		lis, _ = prfI.GetLegalLines()

		wff = prfI.GetWffG()

		for _, li = range lis {
			if li.Rule == pr.Reiteration || !fmla.IsIdentical(li.Wff, wff) {
				continue
			}

			ln, _ = pr.NewLine(li.Wff, nil, pr.Reiteration, 0, nil, li.Ln)

			tot += prfI.InsertLine(ln)

		}
	}

	return
}

// Rules of Positive Propositional Logic (PPL)

var wedgeIntroFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI           []*pr.Proof
		prfI            *pr.Proof
		wffs            []*fmla.WffTree
		lenW            int
		wff, subL, subR *fmla.WffTree
		lis             []*pr.LineInfo
		ji1, ji2        *pr.LineInfo
		ln              *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		if wffs, lenW = prfI.GetLegalSubformulae(fmla.Wedge); lenW == 0 {
			continue
		}

		lis, _ = prfI.GetLegalLines()

		for _, wff = range wffs {
			subL, subR = fmla.GetWffSubformulae(wff)

			for _, ji1 = range lis {
				if !fmla.IsIdentical(ji1.Wff, subL) {
					continue
				}

				for _, ji2 = range lis {
					if !fmla.IsIdentical(ji2.Wff, subR) {
						continue
					}

					ln, _ = pr.NewLine(wff, nil, pr.WedgeIntro, 0, nil, ji1.Ln, ji2.Ln)

					tot += prfI.InsertLine(ln)

					break
				}
			}
		}
	}

	return
}

var wedgeElimFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
		lis   []*pr.LineInfo
		ji1   *pr.LineInfo
		ln    *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		lis, _ = prfI.GetLegalLines()

		for _, ji1 = range lis {
			if ji1.Mop != fmla.Wedge {
				continue
			}

			ln, _ = pr.NewLine(ji1.SubL, nil, pr.WedgeElim, 0, nil, ji1.Ln)

			tot += prfI.InsertLine(ln)

			ln, _ = pr.NewLine(ji1.SubR, nil, pr.WedgeElim, 0, nil, ji1.Ln)

			tot += prfI.InsertLine(ln)
		}
	}

	return
}

var veeIntroFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI           []*pr.Proof
		prfI            *pr.Proof
		wffs            []*fmla.WffTree
		lenW            int
		wff, subL, subR *fmla.WffTree
		lis             []*pr.LineInfo
		ji1             *pr.LineInfo
		ln              *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		if wffs, lenW = prfI.GetLegalSubformulae(fmla.Vee); lenW == 0 {
			continue
		}

		lis, _ = prfI.GetLegalLines()

		for _, wff = range wffs {
			subL, subR = fmla.GetWffSubformulae(wff)

			for _, ji1 = range lis {
				if !fmla.IsIdentical(ji1.Wff, subL) && !fmla.IsIdentical(ji1.Wff, subR) {
					continue
				}

				ln, _ = pr.NewLine(wff, nil, pr.VeeIntro, 0, nil, ji1.Ln)

				tot += prfI.InsertLine(ln)

				break
			}
		}
	}

	return
}

var veeElimFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI         []*pr.Proof
		prfI          *pr.Proof
		lis           []*pr.LineInfo
		ji1, ji2, ji3 *pr.LineInfo
		ln            *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		lis, _ = prfI.GetLegalLines()

		for _, ji1 = range lis {
			if ji1.Mop != fmla.Vee {
				continue
			}

			for _, ji2 = range lis {
				if ji2.Mop != fmla.To || !fmla.IsIdentical(ji2.SubL, ji1.SubL) {
					continue
				}

				for _, ji3 = range lis {
					if ji3.Mop != fmla.To || !fmla.IsIdentical(ji3.SubL, ji1.SubR) {
						continue
					}

					if fmla.IsIdentical(ji2.SubR, ji3.SubR) {
						ln, _ = pr.NewLine(ji2.SubR, nil, pr.VeeElim, 0, nil, ji1.Ln, ji2.Ln, ji3.Ln)

						tot += prfI.InsertLine(ln)
					}
				}
			}
		}
	}

	return
}

var iffIntroFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI           []*pr.Proof
		prfI            *pr.Proof
		lis             []*pr.LineInfo
		wff, subL, subR *fmla.WffTree
		ji1, ji2        *pr.LineInfo
		ln              *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		if wff = prfI.GetWffG(); fmla.GetWffMop(wff) != fmla.Iff {
			continue
		}

		subL, subR = fmla.GetWffSubformulae(wff)

		lis, _ = prfI.GetLegalLines()

		for _, ji1 = range lis {
			if ji1.Mop != fmla.To || !fmla.IsIdentical(ji1.SubL, subL) || !fmla.IsIdentical(ji1.SubR, subR) {
				continue
			}

			for _, ji2 = range lis {
				if ji2.Mop != fmla.To || !fmla.IsIdentical(ji2.SubL, subR) || !fmla.IsIdentical(ji2.SubR, subL) {
					continue
				}

				ln, _ = pr.NewLine(wff, nil, pr.IffIntro, 0, nil, ji1.Ln, ji2.Ln)

				tot += prfI.InsertLine(ln)
			}
		}
	}

	return
}

var iffElimFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
		lis   []*pr.LineInfo
		ji1   *pr.LineInfo
		wff   *fmla.WffTree
		ln    *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		lis, _ = prfI.GetLegalLines()

		for _, ji1 = range lis {
			if ji1.Mop != fmla.Iff {
				continue
			}

			wff = fmla.NewCompositeWff(fmla.To, ji1.SubL, ji1.SubR, 0, 0)

			ln, _ = pr.NewLine(wff, nil, pr.IffElim, 0, nil, ji1.Ln)

			tot += prfI.InsertLine(ln)

			wff = fmla.NewCompositeWff(fmla.To, ji1.SubR, ji1.SubL, 0, 0)

			ln, _ = pr.NewLine(wff, nil, pr.IffElim, 0, nil, ji1.Ln)

			tot += prfI.InsertLine(ln)
		}
	}

	return
}

// Rules of Minimal Propositional Logic (MPL)

var botIntroFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI    []*pr.Proof
		prfI     *pr.Proof
		lis      []*pr.LineInfo
		ji1, ji2 *pr.LineInfo
		wff      *fmla.WffTree
		ln       *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		lis, _ = prfI.GetLegalLines()

		for _, ji2 = range lis {
			if ji2.Pred == fmla.Bot {
				break
			}

			if ji2.Mop != fmla.Neg {
				continue
			}

			for _, ji1 = range lis {
				if !fmla.IsIdentical(ji1.Wff, ji2.SubL) {
					continue
				}

				wff = fmla.NewAtomicWff(fmla.Bot)

				ln, _ = pr.NewLine(wff, nil, pr.BotIntro, 0, nil, ji1.Ln, ji2.Ln)

				tot += prfI.InsertLine(ln)

				break
			}
		}
	}

	return
}

var negIntroFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI    []*pr.Proof
		prfI     *pr.Proof
		purp     pr.NDRule
		is       bool
		ji1, ji2 *pr.LineInfo
		wff      *fmla.WffTree
		ln       *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)

	for _, prfI = range prfsI {
		if purp = prfI.GetPurpose(); purp != pr.NegIntro || !prfI.IsOpen() {
			continue
		}

		if ji2, is = prfI.IsWffGMet(); !is {
			continue
		}

		ji1 = prfI.GetFirstLine()

		wff = fmla.NewCompositeWff(fmla.Neg, ji1.Wff, nil, 0, 0)

		ln, _ = pr.NewLine(wff, nil, pr.NegIntro, 0, nil, ji1.Ln, ji2.Ln)

		tot += ji2.PrfO.InsertLine(ln)

		_ = prfI.CloseProof()
	}

	return
}

// Rules of Intuitionistic Propositional Logic (IPL)

var botElimFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
		lis   []*pr.LineInfo
		ji1   *pr.LineInfo
		wff   *fmla.WffTree
		ln    *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		lis, _ = prfI.GetLegalLines()

		for _, ji1 = range lis {
			if ji1.Pred != fmla.Bot {
				continue
			}

			wff = prfI.GetWffG()

			ln, _ = pr.NewLine(wff, nil, pr.BotElim, 0, nil, ji1.Ln)

			tot += prfI.InsertLine(ln)
		}
	}

	return
}

// Rules of Classical Propositional Logic (CPL)

var negElimFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
		lis   []*pr.LineInfo
		ji1   *pr.LineInfo
		wff   *fmla.WffTree
		ln    *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		lis, _ = prfI.GetLegalLines()

		for _, ji1 = range lis {
			if ji1.Mop != fmla.Neg || fmla.GetWffMop(ji1.SubL) != fmla.Neg {
				continue
			}

			wff, _ = fmla.GetWffSubformulae(ji1.SubL)

			ln, _ = pr.NewLine(wff, nil, pr.NegElim, 0, nil, ji1.Ln)

			tot += prfI.InsertLine(ln)
		}
	}

	return
}

// Rules of Quantificational Logic (QL)

var forAllIntroFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI    []*pr.Proof
		prfI     *pr.Proof
		purp     pr.NDRule
		is       bool
		ji1, ji2 *pr.LineInfo
		apc, pv  fmla.Predicate
		aac, av  fmla.Argument
		pvs      []fmla.Predicate
		avs      []fmla.Argument
		wff      *fmla.WffTree
		ln       *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)

	for _, prfI = range prfsI {
		if purp = prfI.GetPurpose(); purp != pr.ForAllIntro || !prfI.IsOpen() {
			continue
		}

		if ji2, is = prfI.IsWffGMet(); !is {
			continue
		}

		ji1 = prfI.GetFirstLine()

		apc, aac = prfI.GetArbitraryConstants()

		pvs, avs = prfI.GetLegalVariables()

		switch {
		case apc != 0:
			for _, pv = range pvs {
				if fmla.HasPred(ji2.Wff, pv) {
					continue
				}

				wff = fmla.GeneralizePred(fmla.ForAll, ji2.Wff, apc, pv)

				ln, _ = pr.NewLine(wff, nil, pr.ForAllIntro, 0, nil, ji1.Ln, ji2.Ln)

				tot += ji2.PrfO.InsertLine(ln)
			}
		case aac != 0:
			for _, av = range avs {
				if fmla.HasArg(ji2.Wff, av) {
					continue
				}

				wff = fmla.GeneralizeArg(fmla.ForAll, ji2.Wff, aac, av)

				ln, _ = pr.NewLine(wff, nil, pr.ForAllIntro, 0, nil, ji1.Ln, ji2.Ln)

				tot += ji2.PrfO.InsertLine(ln)
			}
		}

		_ = prfI.CloseProof()
	}

	return
}

var forAllElimFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI   []*pr.Proof
		prfI    *pr.Proof
		lis     []*pr.LineInfo
		pcs     []fmla.Predicate
		acs     []fmla.Argument
		li      *pr.LineInfo
		pc, apc fmla.Predicate
		ac, aac fmla.Argument
		wff     *fmla.WffTree
		ln      *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		lis, _ = prfI.GetLegalLines()

		pcs, acs, apc, aac = prfI.GetLegalConstants()

		// fmt.Printf("DEBUG: The available constants for ForAllElim are: %c, %c, %c, %c\n", pcs, acs, apc, aac)

		for _, li = range lis {
			if li.Mop != fmla.ForAll {
				continue
			}

			switch {
			case li.PV != 0:
				for _, pc = range pcs {
					wff = fmla.Instantiate(li.Wff, pc, 0)

					ln, _ = pr.NewLine(wff, nil, pr.ForAllElim, 0, nil, li.Ln)

					tot += prfI.InsertLine(ln)
				}

				if tot == 0 {
					wff = fmla.Instantiate(li.Wff, apc, 0)

					ln, _ = pr.NewLine(wff, nil, pr.ForAllElim, 0, nil, li.Ln)

					tot += prfI.InsertLine(ln)
				}
			case li.AV != 0:
				for _, ac = range acs {
					wff = fmla.Instantiate(li.Wff, 0, ac)

					ln, _ = pr.NewLine(wff, nil, pr.ForAllElim, 0, nil, li.Ln)

					tot += prfI.InsertLine(ln)
				}

				if tot == 0 {
					wff = fmla.Instantiate(li.Wff, 0, aac)

					ln, _ = pr.NewLine(wff, nil, pr.ForAllElim, 0, nil, li.Ln)

					tot += prfI.InsertLine(ln)
				}
			}
		}
	}

	return
}

var existsIntroFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI     []*pr.Proof
		prfI      *pr.Proof
		wffs      []*fmla.WffTree
		lenW      int
		wff, wffI *fmla.WffTree
		lis       []*pr.LineInfo
		ji1       *pr.LineInfo
		pv, pc    fmla.Predicate
		av, ac    fmla.Argument
		pcs       []fmla.Predicate
		acs       []fmla.Argument
		ln        *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		if wffs, lenW = prfI.GetLegalSubformulae(fmla.Exists); lenW == 0 {
			continue
		}

		lis, _ = prfI.GetLegalLines()

		for _, wff = range wffs {
			pv, av = fmla.GetWffVars(wff)

			for _, ji1 = range lis {
				pcs, acs = fmla.GetConstants(ji1.Wff)

				switch {
				case pv != 0:
					for _, pc = range pcs {
						if wffI = fmla.Instantiate(wff, pc, 0); !fmla.IsIdentical(wffI, ji1.Wff) {
							continue
						}

						ln, _ = pr.NewLine(wff, nil, pr.ExistsIntro, 0, nil, ji1.Ln)

						tot += prfI.InsertLine(ln)
					}
				case av != 0:
					for _, ac = range acs {
						if wffI = fmla.Instantiate(wff, 0, ac); !fmla.IsIdentical(wffI, ji1.Wff) {
							continue
						}

						ln, _ = pr.NewLine(wff, nil, pr.ExistsIntro, 0, nil, ji1.Ln)

						tot += prfI.InsertLine(ln)
					}
				}
			}
		}
	}

	return
}

var existsElimFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI    []*pr.Proof
		prfI     *pr.Proof
		purp     pr.NDRule
		lis      []*pr.LineInfo
		ji2, ji3 *pr.LineInfo
		wff      *fmla.WffTree
		ln       *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)

	for _, prfI = range prfsI {
		if purp = prfI.GetPurpose(); purp != pr.ExistsElim || !prfI.IsOpen() {
			continue
		}

		lis, _ = prfI.GetLocalLines()

		ji2 = prfI.GetFirstLine()

		wff = prfI.GetWffG()

		for _, ji3 = range lis {
			if !fmla.IsIdentical(ji3.Wff, wff) {
				continue
			}

			ln, _ = pr.NewLine(wff, nil, pr.ExistsElim, 0, nil, ji2.J1, ji2.Ln, ji3.Ln)

			tot += ji3.PrfO.InsertLine(ln)

			_ = prfI.CloseProof()

			break
		}
	}

	return
}

// Rules of Quantificational Logic With Identity:

var equalsIntroFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
		lis   []*pr.LineInfo
		acs   []fmla.Argument
		ac    fmla.Argument
		ji1   *pr.LineInfo
		wff   *fmla.WffTree
		ln    *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		lis, _ = prfI.GetLegalLines()

		for _, ji1 = range lis {
			if ji1.Mop != fmla.NoSymbol || ji1.Pred != fmla.Equals {
				continue
			}
		}

		_, acs = fmla.GetConstants(ji1.Wff)

		for _, ac = range acs {
			wff = fmla.NewAtomicWff(fmla.Equals, ac, ac)

			ln, _ = pr.NewLine(wff, nil, pr.EqualsIntro, 0, nil)

			tot += prfI.InsertLine(ln)
		}
	}

	return
}

var equalsElimFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI    []*pr.Proof
		prfI     *pr.Proof
		lis      []*pr.LineInfo
		ji1, ji2 *pr.LineInfo
		acs      []fmla.Argument
		wffs     []*fmla.WffTree
		wff      *fmla.WffTree
		ln       *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		lis, _ = prfI.GetLegalLines()

		for _, ji2 = range lis {
			if ji2.Mop != fmla.NoSymbol || ji2.Pred != fmla.Equals {
				continue
			}

			// Don't do anything if the constants are the same.
			if _, acs, _ = fmla.GetWffPredAndArgs(ji2.Wff); acs[0] == acs[1] {
				continue
			}

			for _, ji1 = range lis {
				wffs = fmla.ReplaceEachArgOnce(ji1.Wff, acs[0], acs[1])

				for _, wff = range wffs {
					if fmla.IsIdentical(wff, ji1.Wff) {
						continue
					}

					ln, _ = pr.NewLine(wff, nil, pr.EqualsElim, 0, nil, ji2.Ln, ji1.Ln)

					tot += prfI.InsertLine(ln)
				}

				wffs = fmla.ReplaceEachArgOnce(ji1.Wff, acs[1], acs[0])

				for _, wff = range wffs {
					if fmla.IsIdentical(wff, ji1.Wff) {
						continue
					}

					ln, _ = pr.NewLine(wff, nil, pr.EqualsElim, 0, nil, ji2.Ln, ji1.Ln)

					tot += prfI.InsertLine(ln)
				}
			}
		}
	}

	return
}

// Rules of Positive Modal Logic:

var boxIntroFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI    []*pr.Proof
		prfI     *pr.Proof
		purp     pr.NDRule
		is       bool
		ji1, ji2 *pr.LineInfo
		wff      *fmla.WffTree
		ln       *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)

	for _, prfI = range prfsI {
		if purp = prfI.GetPurpose(); purp != pr.BoxIntro || !prfI.IsOpen() {
			continue
		}

		if ji2, is = prfI.IsWffGMet(); !is {
			continue
		}

		ji1 = prfI.GetFirstLine()

		wff = fmla.NewCompositeWff(fmla.Box, ji2.Wff, nil, 0, 0)

		ln, _ = pr.NewLine(wff, nil, pr.BoxIntro, 0, nil, ji1.Ln, ji2.Ln)

		tot += ji2.PrfO.InsertLine(ln)

		_ = prfI.CloseProof()
	}

	return
}

var boxElimFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
		purp  pr.NDRule
		lis   []*pr.LineInfo
		ji1   *pr.LineInfo
		wff   *fmla.WffTree
		ln    *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)

	for _, prfI = range prfsI {
		if purp = prfI.GetPurpose(); (purp != pr.BoxIntro && purp != pr.DiamondElim) || !prfI.IsOpen() {
			continue
		}

		lis, _ = prfI.GetLegalLines()

		for _, ji1 = range lis {
			if ji1.Mop != fmla.Box {
				continue
			}

			wff, _ = fmla.GetWffSubformulae(ji1.Wff)

			ln, _ = pr.NewLine(wff, nil, pr.BoxElim, 0, nil, ji1.Ln)

			tot += prfI.InsertLine(ln)
		}

		// Deal with the case of negated diamonds:
		if pr.Positive < drv.InfS { // At least minimal...
			for _, ji1 = range lis {
				if ji1.Mop != fmla.Neg || ji1.MopL != fmla.Diamond {
					continue
				}

				wff, _ = fmla.GetWffSubformulae(ji1.SubL)
				wff = fmla.NewCompositeWff(fmla.Neg, wff, nil, 0, 0)

				ln, _ = pr.NewLine(wff, nil, pr.BoxElim, 0, nil, ji1.Ln)

				tot += prfI.InsertLine(ln)
			}
		}
	}

	return
}

var diamondElimFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI          []*pr.Proof
		wff, subL, bot *fmla.WffTree
		prfI           *pr.Proof
		purp           pr.NDRule
		lis            []*pr.LineInfo
		ji2, ji3       *pr.LineInfo
		mop            fmla.Symbol
		ln             *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)

	bot = fmla.NewAtomicWff(fmla.Bot)

	for _, prfI = range prfsI {
		if purp = prfI.GetPurpose(); purp != pr.DiamondElim || !prfI.IsOpen() {
			continue
		}

		lis, _ = prfI.GetLocalLines()

		ji2 = prfI.GetFirstLine()

		wff = prfI.GetWffG()

		if mop = fmla.GetWffMop(wff); mop == fmla.Diamond {
			subL, _ = fmla.GetWffSubformulae(wff)

			for _, ji3 = range lis {
				if !fmla.IsIdentical(ji3.Wff, subL) {
					continue
				}

				ln, _ = pr.NewLine(wff, nil, pr.DiamondElim, 0, nil, ji2.J1, ji2.Ln, ji3.Ln)

				tot += ji3.PrfO.InsertLine(ln)

				_ = prfI.CloseProof()
			}
		} else if fmla.IsIdentical(wff, bot) && pr.Positive < drv.InfS { // At least Minimal...
			for _, ji3 = range lis {
				if !fmla.IsIdentical(ji3.Wff, bot) {
					continue
				}

				wff = fmla.NewUnaryChainWff([]fmla.Symbol{fmla.Neg, fmla.Diamond}, ji2.Wff)

				ln, _ = pr.NewLine(wff, nil, pr.DiamondElim, 0, nil, ji2.J1, ji2.Ln, ji3.Ln)

				tot += ji3.PrfO.InsertLine(ln)

				_ = prfI.CloseProof()
			}
		}
	}

	return
}

// Rules of Classical Modal Logic:

var diamondIntroFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI       []*pr.Proof
		prfI, prfII *pr.Proof
		lis         []*pr.LineInfo
		ji1         *pr.LineInfo
		wff         *fmla.WffTree
		ln          *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		lis, _ = prfI.GetLocalLines()

		for _, ji1 = range lis {
			if ji1.Mop != fmla.Neg || ji1.MopL != fmla.Box {
				continue
			}

			wff, _ = fmla.GetWffSubformulae(ji1.SubL)
			wff = fmla.NewUnaryChainWff([]fmla.Symbol{fmla.Diamond, fmla.Neg}, wff)

			ln, _ = pr.NewLine(wff, nil, pr.DiamondIntro, 0, nil, ji1.Ln)

			tot += prfI.InsertLine(ln)

			wff, _ = fmla.GetWffSubformulae(wff)

			_, prfII = pr.NewLine(wff, ji1.WffG, pr.Assumption, pr.DiamondElim, prfI, ln)

			tot += prfI.InsertInnerProof(prfII)
		}
	}

	return
}

// Rules of Modal Logics K, D, M, 4, B:

var introKFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
		lis   []*pr.LineInfo
		ji1   *pr.LineInfo
		wff   *fmla.WffTree
		ln    *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		lis, _ = prfI.GetLocalLines()

		for _, ji1 = range lis {
			if !ji1.Prf.IsTheorem(ji1.Ln) {
				continue
			}

			wff = fmla.NewCompositeWff(fmla.Box, ji1.Wff, nil, 0, 0)

			ln, _ = pr.NewLine(wff, nil, pr.IntroK, 0, nil, ji1.Ln)

			tot += prfI.InsertLine(ln)
		}
	}

	return
}

var elimDFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
		lis   []*pr.LineInfo
		ji1   *pr.LineInfo
		wff   *fmla.WffTree
		ln    *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		lis, _ = prfI.GetLocalLines()

		for _, ji1 = range lis {
			if ji1.Mop != fmla.Box {
				continue
			}

			wff = fmla.NewCompositeWff(fmla.Diamond, ji1.SubL, nil, 0, 0)

			ln, _ = pr.NewLine(wff, nil, pr.ElimD, 0, nil, ji1.Ln)

			tot += prfI.InsertLine(ln)
		}
	}

	return
}

var introMFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
		wffs  []*fmla.WffTree
		wff   *fmla.WffTree
		lis   []*pr.LineInfo
		ji1   *pr.LineInfo
		ln    *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		if wff = prfI.GetWffG(); !fmla.HasOp(wff, fmla.Diamond) {
			continue
		}

		wffs = fmla.GetAllSubformulae(wff)

		lis, _ = prfI.GetLocalLines()

		for _, wff = range wffs {
			for _, ji1 = range lis {
				if fmla.FindSubformula(wff, ji1.Wff) != "L!" {
					continue
				}

				ln, _ = pr.NewLine(wff, nil, pr.IntroM, 0, nil, ji1.Ln)

				tot += prfI.InsertLine(ln)
			}
		}
	}

	return
}

var elimMFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
		lis   []*pr.LineInfo
		ji1   *pr.LineInfo
		ln    *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		lis, _ = prfI.GetLocalLines()

		for _, ji1 = range lis {
			if ji1.Mop != fmla.Box {
				continue
			}

			ln, _ = pr.NewLine(ji1.SubL, nil, pr.ElimM, 0, nil, ji1.Ln)

			tot += prfI.InsertLine(ln)
		}
	}

	return
}

var intro4Func ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
		lis   []*pr.LineInfo
		wff   *fmla.WffTree
		count uint
		ji1   *pr.LineInfo
		ln    *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		wff = prfI.GetWffG()

		if count = fmla.CountOps(wff, fmla.Box); count < 2 {
			continue
		}

		lis, _ = prfI.GetLocalLines()

		for _, ji1 = range lis {
			if ji1.Mop != fmla.Box || count < fmla.CountOps(ji1.Wff, fmla.Box)+1 {
				continue
			}

			wff = fmla.NewCompositeWff(fmla.Box, ji1.Wff, nil, 0, 0)

			ln, _ = pr.NewLine(wff, nil, pr.Intro4, 0, nil, ji1.Ln)

			tot += prfI.InsertLine(ln)
		}
	}

	return
}

var elim4Func ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
		lis   []*pr.LineInfo
		ji1   *pr.LineInfo
		ln    *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		lis, _ = prfI.GetLocalLines()

		for _, ji1 = range lis {
			if ji1.Mop != fmla.Diamond || ji1.MopL != fmla.Diamond {
				continue
			}

			ln, _ = pr.NewLine(ji1.SubL, nil, pr.Elim4, 0, nil, ji1.Ln)

			tot += prfI.InsertLine(ln)
		}
	}

	return
}

var introBFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
		wff   *fmla.WffTree
		count uint
		lis   []*pr.LineInfo
		ji1   *pr.LineInfo
		ln    *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		wff = prfI.GetWffG()

		if count = fmla.CountOps(wff, fmla.Box) + fmla.CountOps(wff, fmla.Diamond); count < 2 {
			continue
		}

		lis, _ = prfI.GetLocalLines()

		for _, ji1 = range lis {
			if count < fmla.CountOps(ji1.Wff, fmla.Box)+fmla.CountOps(ji1.Wff, fmla.Diamond)+2 {
				continue
			}

			wff = fmla.NewUnaryChainWff([]fmla.Symbol{fmla.Box, fmla.Diamond}, ji1.Wff)

			ln, _ = pr.NewLine(wff, nil, pr.IntroB, 0, nil, ji1.Ln)

			tot += prfI.InsertLine(ln)
		}
	}

	return
}

var elimBFunc ndRuleFunc = func(drv *Derivation) (tot int) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
		lis   []*pr.LineInfo
		ji1   *pr.LineInfo
		wff   *fmla.WffTree
		ln    *pr.Line
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		lis, _ = prfI.GetLocalLines()

		for _, ji1 = range lis {
			if ji1.Mop != fmla.Diamond || ji1.MopL != fmla.Box {
				continue
			}

			wff, _ = fmla.GetWffSubformulae(ji1.SubL)

			ln, _ = pr.NewLine(wff, nil, pr.ElimB, 0, nil, ji1.Ln)

			tot += prfI.InsertLine(ln)
		}
	}

	return
}

func pushRules(drv *Derivation) (tot int) {
	if pr.NoInference < drv.InfS { // At least Implicational...
		tot += topIntroFunc(drv)                                         // Zero premises, one hook.
		tot += reiterationFunc(drv) + toElimFunc(drv) + toIntroFunc(drv) // Two premises.
	}

	if pr.Implicational < drv.InfS { // At least Positive...
		tot += wedgeElimFunc(drv) + veeIntroFunc(drv) + iffElimFunc(drv) // One premise.
		tot += wedgeIntroFunc(drv) + iffIntroFunc(drv)                   // Two premises.
		tot += veeElimFunc(drv)                                          // Three premises.

		// Quantificational logics...
		tot += forAllElimFunc(drv) + existsIntroFunc(drv) + equalsIntroFunc(drv) // One premise.
		tot += forAllIntroFunc(drv) + equalsElimFunc(drv)                        // Two premises.
		tot += existsElimFunc(drv)                                               // Three premises.

		// System-Free Modal Logics...
		if pr.IsAllowedModality(pr.BoxIntro, drv.ModS) {
			tot += boxElimFunc(drv)     // One premise.
			tot += boxIntroFunc(drv)    // Two premises.
			tot += diamondElimFunc(drv) // Three premises.
		}

		// System K Modal Logics
		if pr.IsAllowedModality(pr.IntroK, drv.ModS) {
			tot += introKFunc(drv) // One premise.
		}

		// System D Modal Logics
		if pr.IsAllowedModality(pr.ElimD, drv.ModS) {
			tot += elimDFunc(drv) // One premise.
		}

		// System M Modal Logics
		if pr.IsAllowedModality(pr.IntroM, drv.ModS) {
			tot += elimMFunc(drv) + introMFunc(drv) // One premise.
		}

		// System 4 Modal Logics
		if pr.IsAllowedModality(pr.Intro4, drv.ModS) {
			tot += elim4Func(drv) + intro4Func(drv) // One premise.
		}

		// System B Modal Logics
		if pr.IsAllowedModality(pr.IntroB, drv.ModS) {
			tot += elimBFunc(drv) + introBFunc(drv) // One premise.
		}
	}

	if pr.Positive < drv.InfS { // At least Minimal...
		tot += botIntroFunc(drv) + negIntroFunc(drv) // Two premises.
	}

	if pr.Minimal < drv.InfS { // At least Intuitionistic...
		tot += botElimFunc(drv) // One premise.
	}

	if pr.Intuitionistic < drv.InfS { // At least Classical...
		tot += negElimFunc(drv) // One premise.

		if pr.IsAllowedModality(pr.DiamondIntro, drv.ModS) {
			tot += diamondIntroFunc(drv) // One premise.
		}
	}

	return
}
