package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
	"fmt"
	"iter"
	"slices"
	"strings"
)

type ndRuleFunc func(drv *Deriver) (tot int)

// Rules of Implicational Propositional Logic (TPL)

var topIntroFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		wff  *fmla.Wff
		prfs []*pr.Proof
		prf  *pr.Proof
	)

	wff = fmla.NewAtomicWff(fmla.Top)

	prfs = drv.Prf.GetAllProofs()

	for _, prf = range prfs {
		if !prf.IsOpen() {
			continue
		}

		tot += prf.InsertNewLine(wff, pr.TopIntro, 0)
	}

	return
}

var toIntroFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		prfO, prfI *pr.Proof
		prfsI      []*pr.Proof
		j1, j2     *pr.Line
		wffG, wff  *fmla.Wff
		has        bool
	)

	prfsI = drv.Prf.GetInnerProofs(false)

	for _, prfI = range prfsI {
		if !prfI.IsOpen() || prfI.GetPurp() != pr.ToIntro {
			continue
		}

		if j1 = prfI.GetLineAtIndex(0); j1 == nil {
			continue
		}

		wffG = prfI.GetWffG()

		if j2, has = prfI.HasWffInLines(wffG); !has {
			continue
		} else {
			_ = prfI.MinimizeProof()
		}

		wff = j1.GetWff()
		wff = fmla.NewBinaryWff(fmla.To, wff, wffG)

		prfO = prfI.GetOuterProof()

		tot += prfO.InsertNewLine(wff, pr.ToIntro, 0, j1, j2)

		_ = prfI.CloseProof()
	}

	return
}

func helpToElimFunc(drv *Deriver) (tot int) {
	var (
		liSeq      iter.Seq[*lineInfo]
		li         *lineInfo
		wffA, wffB *fmla.Wff
		prfsN      []*pr.Proof
		prfN       *pr.Proof
		ok         bool
	)

	liSeq = genLineInfoSeq(drv.Prf)

	for li = range liSeq {
		if li.ln.IsExtended() || fmla.GetWffMop(li.wff) != fmla.To {
			continue
		}

		if pr.NoInference < drv.InfS { // At least TPL...
			wffA, wffB = fmla.GetWffSubformulae(li.wff)

			prfsN = getOpenInnerProofs(li.prf, innerToOuterSort)

			for _, prfN = range prfsN {
				if _, ok = prfN.HasWffInLines(wffB); !ok {
					tot += drv.pushAssumptions(wffA, prfN)
				}
			}
		}

		_ = li.ln.SetExtended(true)
	}

	return
}

var toElimFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		liPairs  iter.Seq2[*lineInfo, *lineInfo]
		ji1, ji2 *lineInfo
		sub, wff *fmla.Wff
	)

	liPairs = genLineInfoPairs(drv.Prf, 0)

	for ji1, ji2 = range liPairs {
		if fmla.GetWffMop(ji1.wff) == fmla.To {
			if sub, wff = fmla.GetWffSubformulae(ji1.wff); fmla.IsIdentical(sub, ji2.wff) {
				tot += ji2.prf.InsertNewLine(wff, pr.ToElim, 0, ji1.ln, ji2.ln)

				if ji1.prf == ji2.prf {
					_ = ji1.ln.SetExtended(true)
				}
			}
		}

		if fmla.GetWffMop(ji2.wff) == fmla.To {
			if sub, wff = fmla.GetWffSubformulae(ji2.wff); fmla.IsIdentical(sub, ji1.wff) {
				tot += ji2.prf.InsertNewLine(wff, pr.ToElim, 0, ji2.ln, ji1.ln)

				_ = ji2.ln.SetExtended(true)
			}
		}
	}

	if tot == 0 {
		tot += helpToElimFunc(drv)
	}

	return
}

var reiterationFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		liPairs  iter.Seq2[*lineInfo, *lineInfo]
		ji1, ji2 *lineInfo
		wffG     *fmla.Wff
	)

	liPairs = genLineInfoPairs(drv.Prf, 0)

	for ji1, ji2 = range liPairs {
		if ji1.prf.GetProofDistance(ji2.prf) < 1 {
			continue
		}

		if wffG = ji2.prf.GetWffG(); !fmla.IsIdentical(ji1.wff, wffG) {
			continue
		}

		tot += ji2.prf.InsertNewLine(ji1.wff, pr.Reiteration, 0, ji1.ln)
	}

	return
}

// Rules of Positive Propositional Logic (PPL)

var wedgeIntroFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		prfWffPairs iter.Seq2[*pr.Proof, *fmla.Wff]
		liPairs     iter.Seq2[*lineInfo, *lineInfo]
		prf         *pr.Proof
		ji1, ji2    *lineInfo
		wffP, wff   *fmla.Wff
	)

	prfWffPairs = genProofWffPairs(drv.Prf)

	for prf, wffP = range prfWffPairs {
		if !fmla.HasOp(wffP, fmla.Wedge) {
			continue
		}

		liPairs = genLineInfoPairs(prf, 0)

		for ji1, ji2 = range liPairs {
			if wff = fmla.NewBinaryWff(fmla.Wedge, ji1.wff, ji1.wff); fmla.HasSubformula(wffP, wff) {
				tot += ji1.prf.InsertNewLine(wff, pr.WedgeIntro, 0, ji1.ln, ji1.ln)
			}

			if wff = fmla.NewBinaryWff(fmla.Wedge, ji1.wff, ji2.wff); fmla.HasSubformula(wffP, wff) {
				tot += ji2.prf.InsertNewLine(wff, pr.WedgeIntro, 0, ji1.ln, ji2.ln)
			}

			if wff = fmla.NewBinaryWff(fmla.Wedge, ji2.wff, ji1.wff); fmla.HasSubformula(wffP, wff) {
				tot += ji2.prf.InsertNewLine(wff, pr.WedgeIntro, 0, ji2.ln, ji1.ln)
			}

			if wff = fmla.NewBinaryWff(fmla.Wedge, ji2.wff, ji2.wff); fmla.HasSubformula(wffP, wff) {
				tot += ji2.prf.InsertNewLine(wff, pr.WedgeIntro, 0, ji2.ln, ji2.ln)
			}
		}
	}

	return
}

var wedgeElimFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		liSeq      iter.Seq[*lineInfo]
		ji1        *lineInfo
		subL, subR *fmla.Wff
	)

	liSeq = genLineInfoSeq(drv.Prf)

	for ji1 = range liSeq {
		if fmla.GetWffMop(ji1.wff) != fmla.Wedge {
			continue
		}

		subL, subR = fmla.GetWffSubformulae(ji1.wff)

		tot += ji1.prf.InsertNewLine(subL, pr.WedgeElim, 0, ji1.ln)
		tot += ji1.prf.InsertNewLine(subR, pr.WedgeElim, 0, ji1.ln)

		_ = ji1.ln.SetExtended(true)
	}

	return
}

var veeIntroFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		prfWffPairs           iter.Seq2[*pr.Proof, *fmla.Wff]
		liSeq                 iter.Seq[*lineInfo]
		prf                   *pr.Proof
		ji1                   *lineInfo
		wffP, subL, subR, wff *fmla.Wff
		wffs                  []*fmla.Wff
	)

	prfWffPairs = genProofWffPairs(drv.Prf)

	for prf, wffP = range prfWffPairs {
		if !fmla.HasOp(wffP, fmla.Vee) {
			continue
		}

		wffs = fmla.GetAllSubformulae(wffP)

		for _, wff = range wffs {
			if fmla.GetWffMop(wff) != fmla.Vee || fmla.HasFreeVars(wff) {
				continue
			}

			subL, subR = fmla.GetWffSubformulae(wff)

			liSeq = genLineInfoSeq(prf)

			for ji1 = range liSeq {
				if !fmla.IsIdentical(ji1.wff, subL) && !fmla.IsIdentical(ji1.wff, subR) {
					continue
				}

				tot += ji1.prf.InsertNewLine(wff, pr.VeeIntro, 0, ji1.ln)
			}
		}
	}

	return
}

func helpVeeElimFunc(drv *Deriver) (tot int) {
	var (
		liSeq            iter.Seq[*lineInfo]
		li               *lineInfo
		prfsN            []*pr.Proof
		wffA, wffB, wffG *fmla.Wff
		prfN, prfI       *pr.Proof
		ok               bool
	)

	liSeq = genLineInfoSeq(drv.Prf)

	for li = range liSeq {
		if li.ln.IsExtended() || fmla.GetWffMop(li.wff) != fmla.Vee || li.rule == pr.VeeIntro {
			continue
		}

		wffA, wffB = fmla.GetWffSubformulae(li.wff)

		prfsN = getOpenInnerProofs(li.prf, innerToOuterSort)

		for _, prfN = range prfsN {
			wffG = prfN.GetWffG()

			if prfI, ok = makeNewInnerProof(wffA, wffG, prfN, pr.ToIntro); ok {
				tot += prfN.InsertInnerProofs(prfI) + drv.pushAssumptions(wffG, prfI)
			}

			if prfI, ok = makeNewInnerProof(wffB, wffG, prfN, pr.ToIntro); ok {
				tot += prfN.InsertInnerProofs(prfI) + drv.pushAssumptions(wffG, prfI)
			}
		}

		_ = li.ln.SetExtended(true)
	}

	return
}

var veeElimFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		liPairs                                  iter.Seq2[*lineInfo, *lineInfo]
		liSeq                                    iter.Seq[*lineInfo]
		ji1, ji2, ji3                            *lineInfo
		subL1, subR1, subL2, subR2, subL3, subR3 *fmla.Wff
		prfI                                     *pr.Proof
	)

	liPairs = genLineInfoPairs(drv.Prf, 0)

	for ji1, ji2 = range liPairs {
		if fmla.GetWffMop(ji1.wff) == fmla.Vee && fmla.GetWffMop(ji2.wff) == fmla.To {
			if subL1, subR1 = fmla.GetWffSubformulae(ji1.wff); !fmla.IsIdentical(subL1, subR1) {
				continue
			}

			if subL2, subR2 = fmla.GetWffSubformulae(ji2.wff); fmla.IsIdentical(subL2, subL1) {
				tot += ji2.prf.InsertNewLine(subR2, pr.VeeElim, 0, ji1.ln, ji2.ln, ji2.ln)
			}
		}

		if fmla.GetWffMop(ji1.wff) == fmla.To && fmla.GetWffMop(ji2.wff) == fmla.Vee {
			if subL2, subR2 = fmla.GetWffSubformulae(ji2.wff); !fmla.IsIdentical(subL2, subR2) {
				continue
			}

			if subL1, subR1 = fmla.GetWffSubformulae(ji1.wff); fmla.IsIdentical(subL1, subL2) {
				tot += ji2.prf.InsertNewLine(subR1, pr.VeeElim, 0, ji2.ln, ji1.ln, ji1.ln)
			}
		}
	}

	liPairs = genLineInfoPairs(drv.Prf, 0)

	for ji2, ji3 = range liPairs {
		if fmla.GetWffMop(ji2.wff) != fmla.To || fmla.GetWffMop(ji3.wff) != fmla.To {
			continue
		}

		subL2, subR2 = fmla.GetWffSubformulae(ji2.wff)
		subL3, subR3 = fmla.GetWffSubformulae(ji3.wff)

		liSeq = genLineInfoSeq(ji2.prf)

		for ji1 = range liSeq {
			if fmla.GetWffMop(ji1.wff) != fmla.Vee {
				continue
			}

			if subL1, subR1 = fmla.GetWffSubformulae(ji1.wff); fmla.IsIdentical(subL1, subR1) {
				if fmla.IsIdentical(subL1, subL2) {
					if _, prfI, _ = ji2.prf.IsReachable(ji1.prf); prfI != nil {
						tot += prfI.InsertNewLine(subR2, pr.VeeElim, 0, ji1.ln, ji2.ln, ji2.ln)
					}
				}

				if fmla.IsIdentical(subL1, subL3) {
					if _, prfI, _ = ji3.prf.IsReachable(ji1.prf); prfI != nil {
						tot += prfI.InsertNewLine(subR3, pr.VeeElim, 0, ji1.ln, ji3.ln, ji3.ln)
					}
				}
			} else {
				if !fmla.IsIdentical(subR2, subR3) {
					continue
				}

				if fmla.IsIdentical(subL1, subL2) && fmla.IsIdentical(subR1, subL3) {
					if _, prfI, _ = ji1.prf.IsReachable(ji2.prf); prfI == nil {
						continue
					}

					if _, prfI, _ = prfI.IsReachable(ji3.prf); prfI != nil {
						tot += prfI.InsertNewLine(subR3, pr.VeeElim, 0, ji1.ln, ji2.ln, ji3.ln)
					}
				}

				if fmla.IsIdentical(subL1, subL3) && fmla.IsIdentical(subR1, subL2) {
					if _, prfI, _ = ji1.prf.IsReachable(ji2.prf); prfI == nil {
						continue
					}

					if _, prfI, _ = prfI.IsReachable(ji3.prf); prfI != nil {
						tot += prfI.InsertNewLine(subR3, pr.VeeElim, 0, ji1.ln, ji3.ln, ji2.ln)
					}
				}
			}
		}
	}

	if tot == 0 {
		tot += helpVeeElimFunc(drv)
	}

	return
}

var iffIntroFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		liPairs                         iter.Seq2[*lineInfo, *lineInfo]
		ji1, ji2                        *lineInfo
		mop1, mop2                      fmla.Symbol
		subL1, subR1, subL2, subR2, wff *fmla.Wff
	)

	liPairs = genLineInfoPairs(drv.Prf, 0)

	for ji1, ji2 = range liPairs {
		if mop1, mop2 = fmla.GetWffMop(ji1.wff), fmla.GetWffMop(ji2.wff); mop1 != fmla.To && mop2 != fmla.To {
			continue
		}

		subL1, subR1 = fmla.GetWffSubformulae(ji1.wff)
		subL2, subR2 = fmla.GetWffSubformulae(ji2.wff)

		if mop1 == fmla.To && mop2 == fmla.To {
			if fmla.IsIdentical(subL1, subR2) && fmla.IsIdentical(subR1, subL2) {
				wff = fmla.NewBinaryWff(fmla.Iff, subL1, subR1)

				tot += ji2.prf.InsertNewLine(wff, pr.IffIntro, 0, ji1.ln, ji2.ln)

				wff = fmla.NewBinaryWff(fmla.Iff, subR1, subL1)

				tot += ji2.prf.InsertNewLine(wff, pr.IffIntro, 0, ji2.ln, ji1.ln)
			}
		}

		if mop1 == fmla.To && fmla.IsIdentical(subL1, subR1) {
			wff = fmla.NewBinaryWff(fmla.Iff, subL1, subL1)

			tot += ji1.prf.InsertNewLine(wff, pr.IffIntro, 0, ji1.ln, ji1.ln)
		}

		if mop2 == fmla.To && fmla.IsIdentical(subL2, subR2) {
			wff = fmla.NewBinaryWff(fmla.Iff, subL2, subL2)

			tot += ji2.prf.InsertNewLine(wff, pr.IffIntro, 0, ji2.ln, ji2.ln)
		}
	}

	return
}

var iffElimFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		liSeq           iter.Seq[*lineInfo]
		ji1             *lineInfo
		subL, subR, wff *fmla.Wff
	)

	liSeq = genLineInfoSeq(drv.Prf)

	for ji1 = range liSeq {
		if fmla.GetWffMop(ji1.wff) != fmla.Iff {
			continue
		}

		subL, subR = fmla.GetWffSubformulae(ji1.wff)

		wff = fmla.NewBinaryWff(fmla.To, subL, subR)

		tot += ji1.prf.InsertNewLine(wff, pr.IffElim, 0, ji1.ln)

		wff = fmla.NewBinaryWff(fmla.To, subR, subL)

		tot += ji1.prf.InsertNewLine(wff, pr.IffElim, 0, ji1.ln)

		_ = ji1.ln.SetExtended(true)
	}

	return
}

var topElimFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		liPairs  iter.Seq2[*lineInfo, *lineInfo]
		ji1, ji2 *lineInfo
		top, wff *fmla.Wff
		wffs     []*fmla.Wff
	)

	top = fmla.NewAtomicWff(fmla.Top)

	liPairs = genLineInfoPairs(drv.Prf, 0)

	for ji1, ji2 = range liPairs {
		if fmla.HasSubformula(ji1.wff, ji2.wff) && 1 < fmla.GetWffDepth(ji2.wff) {
			wffs = fmla.ReplaceEachWffOnce(ji1.wff, ji2.wff, top, fmla.Box, fmla.Diamond)

			for _, wff = range wffs {
				tot += ji2.prf.InsertNewLine(wff, pr.TopElim, 0, ji1.ln, ji2.ln)
			}
		}

		if fmla.HasSubformula(ji2.wff, ji1.wff) && 1 < fmla.GetWffDepth(ji1.wff) {
			wffs = fmla.ReplaceEachWffOnce(ji2.wff, ji1.wff, top, fmla.Box, fmla.Diamond)

			for _, wff = range wffs {
				tot += ji2.prf.InsertNewLine(wff, pr.TopElim, 0, ji2.ln, ji1.ln)
			}
		}
	}

	return
}

// Rules of Minimal Propositional Logic (MPL)

func helpBotIntroFunc(drv *Deriver) (tot int) {
	var (
		liSeq iter.Seq[*lineInfo]
		li    *lineInfo
		wffA  *fmla.Wff
		wffG  *fmla.Wff
		mopA  fmla.Symbol
		prfsN []*pr.Proof
		prfN  *pr.Proof
	)

	liSeq = genLineInfoSeq(drv.Prf)

	for li = range liSeq {
		if li.ln.IsExtended() || fmla.GetWffMop(li.wff) != fmla.Neg {
			continue
		}

		wffA, _ = fmla.GetWffSubformulae(li.wff)

		mopA = fmla.GetWffMop(wffA)

		switch {
		case mopA == fmla.Wedge && pr.Positive < drv.InfS: // At least MPL...
			// ¬(A∧B) ⊢ A→¬B, B→¬A
			wffG = fmla.FillTemplateWithLocales("((?)→¬(?))", li.wff, "LL!", "LR!")

			tot += drv.pushAssumptions(wffG, li.prf)

			wffG = fmla.FillTemplateWithLocales("((?)→¬(?))", li.wff, "LR!", "LL!")

			tot += drv.pushAssumptions(wffG, li.prf)

			_ = li.ln.SetExtended(true)

			continue
		case mopA == fmla.Vee && pr.Positive < drv.InfS: // At least MPL...
			// ¬(A∨B) ⊢ ¬A, ¬B
			wffG = fmla.FillTemplateWithLocales("¬(?)", li.wff, "LL!")

			tot += drv.pushAssumptions(wffG, li.prf)

			wffG = fmla.FillTemplateWithLocales("¬(?)", li.wff, "LR!")

			tot += drv.pushAssumptions(wffG, li.prf)

			_ = li.ln.SetExtended(true)

			continue
		case mopA == fmla.To && pr.Positive < drv.InfS: // At least MPL...
			// ¬(A→B) ⊢ A→¬B, B→¬A, ¬B
			wffG = fmla.FillTemplateWithLocales("((?)→¬(?))", li.wff, "LL!", "LR!")

			tot += drv.pushAssumptions(wffG, li.prf)

			wffG = fmla.FillTemplateWithLocales("((?)→¬(?))", li.wff, "LR!", "LL!")

			tot += drv.pushAssumptions(wffG, li.prf)

			wffG = fmla.FillTemplateWithLocales("¬(?)", li.wff, "LR!")

			tot += drv.pushAssumptions(wffG, li.prf)

			if pr.Minimal < drv.InfS { // At least IPL...
				// ¬(A→B) ⊢ ¬¬A
				wffG = fmla.FillTemplateWithLocales("¬¬(?)", li.wff, "LL!")

				tot += drv.pushAssumptions(wffG, li.prf)
			}

			prfsN = getOpenInnerProofs(li.prf, innerToOuterSort)

			for _, prfN = range prfsN {
				tot += drv.pushAssumptions(wffA, prfN)
			}

			_ = li.ln.SetExtended(true)

			continue
		// case mopA == fmla.Iff && pr.Positive < drv.InfS: // At least MPL...
		// // WARNING! Implementing this will cause the system to slow down drastically!
		// 	// ¬(A↔B) ⊢ (A→B)→¬(B→A), (B→A)→¬(A→B), A→¬B, B→¬A
		// 	wffG = fmla.FillTemplateWithLocales("(((?)→(?))→¬((?)→(?)))", li.wff, "LL!", "LR!", "LR!", "LL!")

		// 	tot += drv.pushAssumptions(wffG, li.prf)

		// 	wffG = fmla.FillTemplateWithLocales("(((?)→(?))→¬((?)→(?)))", li.wff, "LR!", "LL!", "LL!", "LR!")

		// 	tot += drv.pushAssumptions(wffG, li.prf)

		// 	wffG = fmla.FillTemplateWithLocales("((?)→¬(?))", li.wff, "LL!", "LR!")

		// 	tot += drv.pushAssumptions(wffG, li.prf)

		// 	wffG = fmla.FillTemplateWithLocales("((?)→¬(?))", li.wff, "LR!", "LL!")

		// 	tot += drv.pushAssumptions(wffG, li.prf)

		// 	_ = li.ln.SetExtended(true)

		// 	continue
		// case mopA == fmla.ForAll && pr.Positive < drv.InfS: // At least M[12]QL...
		// 	// ¬∀[x|X]A ⊢ ¬¬∃[x|X]¬A
		// 	var (
		// 		pv fmla.Predicate
		// 		av fmla.Argument
		// 	)

		// 	if pv, av = fmla.GetWffVars(wffA); pv != 0 {
		// 		wffG = fmla.FillTemplateWithLocales(fmt.Sprintf("¬¬∃%c¬(?)", pv), li.wff, "LL!")
		// 	} else if av != 0 {
		// 		wffG = fmla.FillTemplateWithLocales(fmt.Sprintf("¬¬∃%c¬(?)", av), li.wff, "LL!")
		// 	}

		// 	tot += drv.pushAssumptions(wffG, li.prf)

		// 	_ = li.ln.SetExtended(true)

		// 	continue
		case mopA == fmla.Exists && pr.Positive < drv.InfS: // At least M[12]QL...
			// ¬∃[x|X]A ⊢ ∀[x|X]¬A
			var (
				pv fmla.Predicate
				av fmla.Argument
			)

			if pv, av = fmla.GetWffVars(wffA); pv != 0 {
				wffG = fmla.FillTemplateWithLocales(fmt.Sprintf("∀%c¬(?)", pv), li.wff, "LL!")
			} else if av != 0 {
				wffG = fmla.FillTemplateWithLocales(fmt.Sprintf("∀%c¬(?)", av), li.wff, "LL!")
			}

			tot += drv.pushAssumptions(wffG, li.prf)

			_ = li.ln.SetExtended(true)

			continue
		// case mop == fmla.Box && pr.Classical == drv.InfS: // At least CPL+K...
		case mopA == fmla.Diamond && pr.Positive < drv.InfS && pr.IsAllowedModality(pr.DiamondElim, drv.ModS): // At least MPL+K...
			// ¬◇A ⊢ □¬A
			wffG = fmla.FillTemplateWithLocales("□¬(?)", li.wff, "LL!")

			tot += drv.pushAssumptions(wffG, li.prf)

			_ = li.ln.SetExtended(true)

			continue
		}

		prfsN = getOpenInnerProofs(li.prf, innerToOuterSort)

		for _, prfN = range prfsN {
			tot += drv.pushAssumptions(wffA, prfN)
		}

		_ = li.ln.SetExtended(true)
	}

	return
}

var botIntroFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		wff, subL *fmla.Wff
		liPairs   iter.Seq2[*lineInfo, *lineInfo]
		ji1, ji2  *lineInfo
	)

	wff = fmla.NewAtomicWff(fmla.Bot)

	liPairs = genLineInfoPairs(drv.Prf, 0)

	for ji1, ji2 = range liPairs {
		if fmla.GetWffMop(ji1.wff) == fmla.Neg {
			subL, _ = fmla.GetWffSubformulae(ji1.wff)

			if fmla.IsIdentical(subL, ji2.wff) {
				tot += ji2.prf.InsertNewLine(wff, pr.BotIntro, 0, ji2.ln, ji1.ln)
			}
		}

		if fmla.GetWffMop(ji2.wff) == fmla.Neg {
			subL, _ = fmla.GetWffSubformulae(ji2.wff)

			if fmla.IsIdentical(subL, ji1.wff) {
				tot += ji2.prf.InsertNewLine(wff, pr.BotIntro, 0, ji1.ln, ji2.ln)
			}
		}
	}

	if tot == 0 {
		tot += helpBotIntroFunc(drv)
	}

	return
}

var negIntroFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		wffG, wff  *fmla.Wff
		prfO, prfI *pr.Proof
		prfsI      []*pr.Proof
		j1, j2     *pr.Line
		has        bool
	)

	wffG = fmla.NewAtomicWff(fmla.Bot)

	prfsI = drv.Prf.GetInnerProofs(false)

	for _, prfI = range prfsI {
		if !prfI.IsOpen() || prfI.GetPurp() != pr.NegIntro {
			continue
		}

		if j1 = prfI.GetLineAtIndex(0); j1 == nil {
			continue
		}

		if j2, has = prfI.HasWffInLines(wffG); !has {
			continue
		} else {
			_ = prfI.MinimizeProof()
		}

		wff = j1.GetWff()
		wff = fmla.NewUnaryWff(fmla.Neg, wff)

		prfO = prfI.GetOuterProof()

		tot += prfO.InsertNewLine(wff, pr.NegIntro, 0, j1, j2)

		_ = prfI.CloseProof()
	}

	return
}

// Rules of Intuitionistic Propositional Logic (IPL)

var botElimFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		liSeq iter.Seq[*lineInfo]
		ji1   *lineInfo
		pred  fmla.Predicate
		wff   *fmla.Wff
	)

	liSeq = genLineInfoSeq(drv.Prf)

	for ji1 = range liSeq {
		if fmla.GetWffMop(ji1.wff) != fmla.NoSymbol {
			continue
		}

		if pred, _, _ = fmla.GetWffPredAndArgs(ji1.wff); pred != fmla.Bot {
			continue
		}

		wff = ji1.prf.GetWffG()

		tot += ji1.prf.InsertNewLine(wff, pr.BotElim, 0, ji1.ln)
	}

	return
}

// Rules of Classical Propositional Logic (CPL)

var negElimFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		liSeq iter.Seq[*lineInfo]
		ji1   *lineInfo
		wff   *fmla.Wff
	)

	liSeq = genLineInfoSeq(drv.Prf)

	for ji1 = range liSeq {
		if fmla.GetWffMop(ji1.wff) != fmla.Neg {
			continue
		}

		if wff, _ = fmla.GetWffSubformulae(ji1.wff); fmla.GetWffMop(wff) != fmla.Neg {
			continue
		}

		wff, _ = fmla.GetWffSubformulae(wff)

		tot += ji1.prf.InsertNewLine(wff, pr.NegElim, 0, ji1.ln)
	}

	return
}

// Rules of Quantificational Logic (QL)

var forAllIntroFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		prfs, prfsI     []*pr.Proof
		prf, prfI, prfO *pr.Proof
		wffP, wffG, wff *fmla.Wff
		j1, j2          *pr.Line
		has             bool
		pc, pv          fmla.Predicate
		ac, av          fmla.Argument
		ok              bool
	)

	prfs = drv.Prf.GetAllProofs()

	for _, prf = range prfs {
		if !prf.IsOpen() {
			continue
		}

		if wffP = prf.GetWffG(); !fmla.HasOp(wffP, fmla.ForAll) {
			continue
		}

		prfsI = prf.GetInnerProofs(false)

		for _, prfI = range prfsI {
			if !prfI.IsOpen() || prfI.GetPurp() != pr.ForAllIntro || prf.GetModalDistance(prfI) != 0 {
				continue
			}

			if j1 = prfI.GetLineAtIndex(0); j1 == nil {
				continue
			}

			wffG = prfI.GetWffG()

			if j2, has = prfI.HasWffInLines(wffG); !has {
				continue
			}

			if pc, pv, ok = prfI.GetQLInnerProofPredicates(); ok {
				wff = fmla.GeneralizePred(fmla.ForAll, wffG, pc, pv)

				prfO = prfI.GetOuterProof()

				tot += prfO.InsertNewLine(wff, pr.ForAllIntro, 0, j1, j2)

				_ = prfI.CloseProof()
			} else if ac, av, ok = prfI.GetQLInnerProofArguments(); ok {
				wff = fmla.GeneralizeArg(fmla.ForAll, wffG, ac, av)

				prfO = prfI.GetOuterProof()

				tot += prfO.InsertNewLine(wff, pr.ForAllIntro, 0, j1, j2)

				_ = prfI.CloseProof()
			}
		}
	}

	return
}

func helpForAllElimFunc(drv *Deriver) (tot int) {
	var (
		liSeq      iter.Seq[*lineInfo]
		li         *lineInfo
		pv, pc     fmla.Predicate
		av, ac     fmla.Argument
		ok         bool
		wffA, wffG *fmla.Wff
		prfI       *pr.Proof
	)

	liSeq = genLineInfoSeq(drv.Prf)

	for li = range liSeq {
		if li.ln.IsExtended() || fmla.GetWffMop(li.wff) != fmla.ForAll {
			continue
		}

		if pv, av = fmla.GetWffVars(li.wff); pv != 0 {
			if pc, ok = li.prf.GetFreshPredicate(); ok {
				wffA, wffG = fmla.Instantiate(li.wff, pc, 0), li.prf.GetWffG()

				if prfI, ok = makeNewInnerProof(wffA, wffG, li.prf, pr.ToIntro); ok {
					tot += li.prf.InsertInnerProofs(prfI) + drv.pushAssumptions(wffG, prfI)
				}
			}
		} else if av != 0 {
			if ac, ok = li.prf.GetFreshArgument(); ok {
				wffA, wffG = fmla.Instantiate(li.wff, 0, ac), li.prf.GetWffG()

				if prfI, ok = makeNewInnerProof(wffA, wffG, li.prf, pr.ToIntro); ok {
					tot += li.prf.InsertInnerProofs(prfI) + drv.pushAssumptions(wffG, prfI)
				}
			}
		} else if wffA, _ = fmla.GetWffSubformulae(li.wff); !fmla.HasFreeVars(wffA) {
			wffG = li.prf.GetWffG()

			if prfI, ok = makeNewInnerProof(wffA, wffG, li.prf, pr.ToIntro); ok {
				tot += li.prf.InsertInnerProofs(prfI) + drv.pushAssumptions(wffG, prfI)
			}
		}

		_ = li.ln.SetExtended(true)
	}

	return
}

var forAllElimFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		liPairs         iter.Seq2[*lineInfo, *lineInfo]
		ji1, ji2        *lineInfo
		pcs1, pcs2, pcs []fmla.Predicate
		acs1, acs2, acs []fmla.Argument
		wffsToWffsI     map[*fmla.Wff][]*fmla.Wff
		wff, wffI       *fmla.Wff
		wffsI           []*fmla.Wff
		lenI            int
	)

	liPairs = genLineInfoPairs(drv.Prf, 0)

	for ji1, ji2 = range liPairs {
		switch {
		case fmla.GetWffMop(ji1.wff) == fmla.ForAll:
			pcs1, pcs2 = ji1.prf.GetUsedPredicates(), ji2.prf.GetUsedPredicates()
			acs1, acs2 = ji1.prf.GetUsedArguments(), ji2.prf.GetUsedArguments()

			pcs, acs = append(pcs1, pcs2...), append(acs1, acs2...)

			wffsToWffsI = fmla.GetAllInstantiations(ji1.wff, pcs, acs)

			for wff, wffsI = range wffsToWffsI {
				if !fmla.IsIdentical(wff, ji1.wff) {
					continue
				}

				for _, wffI = range wffsI {
					tot += ji2.prf.InsertNewLine(wffI, pr.ForAllElim, 0, ji1.ln)
				}

				if lenI = len(wffsI); 0 < lenI && ji1.prf == ji2.prf {
					_ = ji1.ln.SetExtended(true)
				}
			}
		case fmla.GetWffMop(ji2.wff) == fmla.ForAll:
			pcs1, pcs2 = ji1.prf.GetUsedPredicates(), ji2.prf.GetUsedPredicates()
			acs1, acs2 = ji1.prf.GetUsedArguments(), ji2.prf.GetUsedArguments()

			pcs, acs = append(pcs1, pcs2...), append(acs1, acs2...)

			wffsToWffsI = fmla.GetAllInstantiations(ji2.wff, pcs, acs)

			for wff, wffsI = range wffsToWffsI {
				if !fmla.IsIdentical(wff, ji2.wff) {
					continue
				}

				for _, wffI = range wffsI {
					tot += ji2.prf.InsertNewLine(wffI, pr.ForAllElim, 0, ji2.ln)
				}

				if lenI = len(wffsI); 0 < lenI {
					_ = ji2.ln.SetExtended(true)
				}
			}
		}
	}

	if tot == 0 {
		tot += helpForAllElimFunc(drv)
	}

	return
}

var existsIntroFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		prfWffPairs     iter.Seq2[*pr.Proof, *fmla.Wff]
		prf, prfI       *pr.Proof
		wffP, wff, wffI *fmla.Wff
		liSeq           iter.Seq[*lineInfo]
		ji1             *lineInfo
		pcs             []fmla.Predicate
		acs             []fmla.Argument
		// lenC            int
		wffsToWffsI map[*fmla.Wff][]*fmla.Wff
		wffsI       []*fmla.Wff
	)

	prfWffPairs = genProofWffPairs(drv.Prf)

	for prf, wffP = range prfWffPairs {
		if !fmla.HasOp(wffP, fmla.Exists) {
			continue
		}

		liSeq = genLineInfoSeq(drv.Prf)

		for ji1 = range liSeq {
			if prf.GetModalDistance(ji1.prf) != 0 && ji1.prf.GetModalDistance(prf) != 0 {
				continue
			}

			if _, prfI, _ = prf.IsReachable(ji1.prf); prfI == nil {
				continue
			}

			pcs, acs = fmla.GetConstants(ji1.wff)

			// Manage vacuous existential introduction by introducing new "alpha" constants
			// that are not part of the standard collection of predicate constants.
			// if lenC = len(pcs); lenC == 0 {
			// 	pcs = append(pcs, fmla.AlphaPred)
			// }

			// if lenC = len(acs); lenC == 0 {
			// 	acs = append(acs, fmla.AlphaArg)
			// }

			wffsToWffsI = fmla.GetAllInstantiations(wffP, pcs, acs)

			for wff, wffsI = range wffsToWffsI {
				if fmla.GetWffMop(wff) != fmla.Exists {
					continue
				}

				for _, wffI = range wffsI {
					if fmla.IsIdentical(ji1.wff, wffI) {
						tot += prfI.InsertNewLine(wff, pr.ExistsIntro, 0, ji1.ln)

						break
					}
				}
			}
		}
	}

	return
}

func helpExistsElimFunc(drv *Deriver) (tot int) {
	var (
		liSeq iter.Seq[*lineInfo]
		li    *lineInfo
		prfI  *pr.Proof
		wffG  *fmla.Wff
		ok    bool
	)

	liSeq = genLineInfoSeq(drv.Prf)

	for li = range liSeq {
		if li.ln.IsExtended() || fmla.GetWffMop(li.wff) != fmla.Exists || li.rule == pr.ExistsElim {
			continue
		}

		wffG = li.prf.GetWffG()

		if prfI, ok = makeNewInnerProof(li.wff, wffG, li.prf, pr.ExistsElim, li.ln); ok {
			tot += li.prf.InsertInnerProofs(prfI) + drv.pushAssumptions(wffG, prfI)
		}

		_ = li.ln.SetExtended(true)
	}

	return
}

var existsElimFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		prfO, prfI *pr.Proof
		wffG       *fmla.Wff
		prfsI      []*pr.Proof
		j1, j2, j3 *pr.Line
		has        bool
	)

	prfsI = drv.Prf.GetInnerProofs(false)

	for _, prfI = range prfsI {
		if !prfI.IsOpen() || prfI.GetPurp() != pr.ExistsElim {
			continue
		}

		j2 = prfI.GetLineAtIndex(0)

		j1 = j2.GetJustifications()[0]

		wffG = prfI.GetWffG()

		if j3, has = prfI.HasWffInLines(wffG); !has {
			continue
		} else {
			_ = prfI.MinimizeProof()
		}

		prfO = prfI.GetOuterProof()

		tot += prfO.InsertNewLine(wffG, pr.ExistsElim, 0, j1, j2, j3)

		_ = prfI.CloseProof()
	}

	if tot == 0 {
		tot += helpExistsElimFunc(drv)
	}

	return
}

// Rules of Quantificational Logic With Identity:

var equalsIntroFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		prfWffPairs iter.Seq2[*pr.Proof, *fmla.Wff]
		prf         *pr.Proof
		wffP, wff   *fmla.Wff
		acs         []fmla.Argument
		ac          fmla.Argument
	)

	prfWffPairs = genProofWffPairs(drv.Prf)

	for prf, wffP = range prfWffPairs {
		_, acs = fmla.GetConstants(wffP)

		for _, ac = range acs {
			wff = fmla.NewAtomicWff(fmla.Equals, ac, ac)

			tot += prf.InsertNewLine(wff, pr.EqualsIntro, 0)
		}
	}

	return
}

var equalsElimFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		liPairs  iter.Seq2[*lineInfo, *lineInfo]
		ji1, ji2 *lineInfo
		pred     fmla.Predicate
		args     []fmla.Argument
		ok       bool
		wffs     []*fmla.Wff
		wff      *fmla.Wff
	)

	liPairs = genLineInfoPairs(drv.Prf, 0)

	for ji1, ji2 = range liPairs {
		if fmla.GetWffMop(ji1.wff) != fmla.NoSymbol && fmla.GetWffMop(ji2.wff) != fmla.NoSymbol {
			continue
		}

		if pred, args, ok = fmla.GetWffPredAndArgs(ji1.wff); ok && pred == fmla.Equals && args[0] != args[1] {
			wffs = fmla.ReplaceEachArgOnce(ji2.wff, args[0], args[1], fmla.Box, fmla.Diamond)

			for _, wff = range wffs {
				tot += ji2.prf.InsertNewLine(wff, pr.EqualsElim, 0, ji1.ln, ji2.ln)
			}

			wffs = fmla.ReplaceEachArgOnce(ji2.wff, args[1], args[0], fmla.Box, fmla.Diamond)

			for _, wff = range wffs {
				tot += ji2.prf.InsertNewLine(wff, pr.EqualsElim, 0, ji2.ln, ji1.ln)
			}
		}

		if pred, args, ok = fmla.GetWffPredAndArgs(ji2.wff); ok && pred == fmla.Equals && args[0] != args[1] {
			wffs = fmla.ReplaceEachArgOnce(ji1.wff, args[0], args[1], fmla.Box, fmla.Diamond)

			for _, wff = range wffs {
				tot += ji2.prf.InsertNewLine(wff, pr.EqualsElim, 0, ji1.ln, ji2.ln)
			}

			wffs = fmla.ReplaceEachArgOnce(ji1.wff, args[1], args[0], fmla.Box, fmla.Diamond)

			for _, wff = range wffs {
				tot += ji2.prf.InsertNewLine(wff, pr.EqualsElim, 0, ji1.ln, ji2.ln)
			}
		}
	}

	return
}

// Rules of Positive and Minimal Modal Logic:

var boxIntroFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		prfO, prfI *pr.Proof
		prfsI      []*pr.Proof
		j1, j2     *pr.Line
		wffG, wff  *fmla.Wff
		has        bool
	)

	prfsI = drv.Prf.GetInnerProofs(false)

	for _, prfI = range prfsI {
		if !prfI.IsOpen() || prfI.GetPurp() != pr.BoxIntro {
			continue
		}

		if j1 = prfI.GetLineAtIndex(0); j1 == nil {
			continue
		}

		wffG = prfI.GetWffG()

		if j2, has = prfI.HasWffInLines(wffG); !has {
			continue
		} else {
			_ = prfI.MinimizeProof()
		}

		wff = j2.GetWff()
		wff = fmla.NewUnaryWff(fmla.Box, wff)

		prfO = prfI.GetOuterProof()

		tot += prfO.InsertNewLine(wff, pr.BoxIntro, 0, j1, j2)

		_ = prfI.CloseProof()
	}

	return
}

var boxElimFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		liPairs   iter.Seq2[*lineInfo, *lineInfo]
		ji1, ji2  *lineInfo
		wff, subL *fmla.Wff
	)

	liPairs = genLineInfoPairs(drv.Prf, 1)

	for ji1, ji2 = range liPairs {
		if fmla.GetWffMop(ji1.wff) == fmla.Box {
			wff, _ = fmla.GetWffSubformulae(ji1.wff)

			tot += ji2.prf.InsertNewLine(wff, pr.BoxElim, 0, ji1.ln)

			continue
		}

		if pr.Positive < drv.InfS && fmla.GetWffMop(ji1.wff) == fmla.Neg {
			if subL, _ = fmla.GetWffSubformulae(ji1.wff); fmla.GetWffMop(subL) != fmla.Diamond {
				continue
			}

			wff, _ = fmla.GetWffSubformulae(subL)
			wff = fmla.NewUnaryWff(fmla.Neg, wff)

			tot += ji2.prf.InsertNewLine(wff, pr.BoxElim, 0, ji1.ln)
		}
	}

	return
}

func helpDiamondElimFunc(drv *Deriver) (tot int) {
	var (
		liSeq            iter.Seq[*lineInfo]
		li               *lineInfo
		wffA, wffB, wffG *fmla.Wff
		wffsG            []*fmla.Wff
		prfsN            []*pr.Proof
		prfN, prfI       *pr.Proof
		ok               bool
	)

	liSeq = genLineInfoSeq(drv.Prf)

	for li = range liSeq {
		if fmla.GetWffMop(li.wff) != fmla.Diamond || li.rule == pr.DiamondElim {
			continue
		}

		prfsN = getOpenInnerProofs(li.prf, innerToOuterSort)

		wffA = fmla.RetrieveSubformula(li.wff, "L!")

		switch drv.InfS {
		case pr.Classical, pr.Intuitionistic, pr.Minimal:
			wffB = fmla.NewAtomicWff(fmla.Bot)

			for _, prfN = range prfsN {
				if wffG = prfN.GetWffG(); fmla.IsIdentical(wffG, wffB) {
					if prfI, ok = makeNewInnerProof(wffA, wffG, prfN, pr.DiamondElim, li.ln); ok {
						tot += prfN.InsertInnerProofs(prfI)
					}
				}
			}

			fallthrough
		case pr.Positive:
			for _, prfN = range prfsN {
				if wffG = prfN.GetWffG(); !fmla.HasOp(wffG, fmla.Diamond) {
					continue
				}

				wffsG = fmla.GetAllSubformulae(wffG)
				wffsG = slices.DeleteFunc(wffsG, func(wff *fmla.Wff) (nix bool) {
					nix = fmla.GetWffMop(wff) != fmla.Diamond

					return
				})

				for _, wffG = range wffsG {
					wffG = fmla.RetrieveSubformula(wffG, "L!")

					if prfI, ok = makeNewInnerProof(wffA, wffG, prfN, pr.DiamondElim, li.ln); ok {
						tot += prfN.InsertInnerProofs(prfI) + drv.pushAssumptions(wffG, prfI)
					}
				}
			}
		}
	}

	return
}

var diamondElimFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		prfO, prfI     *pr.Proof
		bot, wffG, wff *fmla.Wff
		prfsI          []*pr.Proof
		j1, j2, j3     *pr.Line
		has            bool
	)

	bot = fmla.NewAtomicWff(fmla.Bot)

	prfsI = drv.Prf.GetInnerProofs(false)

	for _, prfI = range prfsI {
		if !prfI.IsOpen() || prfI.GetPurp() != pr.DiamondElim {
			continue
		}

		j2 = prfI.GetLineAtIndex(0)

		j1 = j2.GetJustifications()[0]

		wffG = prfI.GetWffG()

		if j3, has = prfI.HasWffInLines(wffG); !has {
			continue
		} else {
			_ = prfI.MinimizeProof()
		}

		prfO = prfI.GetOuterProof()

		if pr.Positive < drv.InfS && fmla.IsIdentical(wffG, bot) {
			wff = j1.GetWff()
			wff = fmla.NewUnaryWff(fmla.Neg, wff)
		} else {
			wff = fmla.NewUnaryWff(fmla.Diamond, wffG)
		}

		tot += prfO.InsertNewLine(wff, pr.DiamondElim, 0, j1, j2, j3)

		_ = prfI.CloseProof()
	}

	if tot == 0 {
		tot += helpDiamondElimFunc(drv)
	}

	return
}

// Rules of Classical Modal Logic K:

var diamondIntroFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		liSeq iter.Seq[*lineInfo]
		ji1   *lineInfo
		s     string
		wff   *fmla.Wff
	)

	liSeq = genLineInfoSeq(drv.Prf)

	for ji1 = range liSeq {
		if fmla.GetWffMop(ji1.wff) != fmla.Neg {
			continue
		}

		if s = fmla.GetWffString(ji1.wff); !strings.HasPrefix(s, "¬□¬") {
			continue
		}

		wff = fmla.FillTemplateWithLocales("◇(?)", ji1.wff, "LLL!")

		tot += ji1.prf.InsertNewLine(wff, pr.DiamondIntro, 0, ji1.ln)
	}

	return
}

var elimDFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		liSeq iter.Seq[*lineInfo]
		ji1   *lineInfo
		wff   *fmla.Wff
	)

	liSeq = genLineInfoSeq(drv.Prf)

	for ji1 = range liSeq {
		if fmla.GetWffMop(ji1.wff) != fmla.Box {
			continue
		}

		wff, _ = fmla.GetWffSubformulae(ji1.wff)
		wff = fmla.NewUnaryWff(fmla.Diamond, wff)

		tot += ji1.prf.InsertNewLine(wff, pr.ElimD, 0, ji1.ln)
	}

	return
}

var introMFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		prfWffPairs     iter.Seq2[*pr.Proof, *fmla.Wff]
		prf             *pr.Proof
		wffG, wffP, wff *fmla.Wff
		maxOps          uint
		liSeq           iter.Seq[*lineInfo]
		ji1             *lineInfo
	)

	prfWffPairs = genProofWffPairs(drv.Prf)

	for prf, wffP = range prfWffPairs {
		if !fmla.HasOp(wffP, fmla.Diamond) {
			continue
		}

		wffG = prf.GetWffG()

		maxOps = fmla.CountOps(wffG, fmla.Box) + fmla.CountOps(wffG, fmla.Diamond) + 1

		liSeq = genLineInfoSeq(prf)

		for ji1 = range liSeq {
			if maxOps < fmla.CountOps(ji1.wff, fmla.Box)+fmla.CountOps(ji1.wff, fmla.Diamond)+1 {
				continue
			}

			if wff = fmla.NewUnaryWff(fmla.Diamond, ji1.wff); fmla.HasSubformula(wffP, wff) {
				tot += ji1.prf.InsertNewLine(wff, pr.IntroM, 0, ji1.ln)
			}
		}
	}

	return
}

var elimMFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		liSeq iter.Seq[*lineInfo]
		ji1   *lineInfo
		wff   *fmla.Wff
	)

	liSeq = genLineInfoSeq(drv.Prf)

	for ji1 = range liSeq {
		if fmla.GetWffMop(ji1.wff) != fmla.Box {
			continue
		}

		wff, _ = fmla.GetWffSubformulae(ji1.wff)

		tot += ji1.prf.InsertNewLine(wff, pr.ElimM, 0, ji1.ln)
	}

	return
}

var intro4Func ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		prfWffPairs     iter.Seq2[*pr.Proof, *fmla.Wff]
		prf             *pr.Proof
		prfsI           []*pr.Proof
		wffG, wffP, wff *fmla.Wff
		maxOps          uint
		liSeq           iter.Seq[*lineInfo]
		ji1             *lineInfo
	)

	prfWffPairs = genProofWffPairs(drv.Prf)

	for prf, wffP = range prfWffPairs {
		if !fmla.HasOp(wffP, fmla.Box) {
			continue
		}

		wffG = prf.GetWffG()

		maxOps = fmla.CountOps(wffG, fmla.Box) + fmla.CountOps(wffG, fmla.Diamond) + 1

		liSeq = genLineInfoSeq(prf)

		for ji1 = range liSeq {
			if fmla.GetWffMop(ji1.wff) != fmla.Box {
				continue
			}

			if maxOps < fmla.CountOps(ji1.wff, fmla.Box)+fmla.CountOps(ji1.wff, fmla.Diamond)+1 {
				continue
			}

			if wff = fmla.NewUnaryWff(fmla.Box, ji1.wff); fmla.HasSubformula(wffP, wff) {
				tot += ji1.prf.InsertNewLine(wff, pr.Intro4, 0, ji1.ln)
			} else if ji1.ln.GetRule() == pr.Intro4 {
				continue
			}

			prfsI = ji1.prf.GetInnerProofsAtModalDistance(false, 1)

			for range prfsI {
				tot += ji1.prf.InsertNewLine(wff, pr.Intro4, 0, ji1.ln)

				break
			}
		}
	}

	return
}

var elim4Func ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		liSeq iter.Seq[*lineInfo]
		ji1   *lineInfo
		wff   *fmla.Wff
	)

	liSeq = genLineInfoSeq(drv.Prf)

	for ji1 = range liSeq {
		if fmla.GetWffMop(ji1.wff) != fmla.Diamond {
			continue
		}

		if wff, _ = fmla.GetWffSubformulae(ji1.wff); fmla.GetWffMop(wff) == fmla.Diamond {
			tot += ji1.prf.InsertNewLine(wff, pr.Elim4, 0, ji1.ln)
		}
	}

	return
}

var introBFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		prfWffPairs     iter.Seq2[*pr.Proof, *fmla.Wff]
		prf             *pr.Proof
		prfsI           []*pr.Proof
		wffG, wffP, wff *fmla.Wff
		maxOps          uint
		liSeq           iter.Seq[*lineInfo]
		ji1             *lineInfo
	)

	prfWffPairs = genProofWffPairs(drv.Prf)

	for prf, wffP = range prfWffPairs {
		if !fmla.HasOp(wffP, fmla.Box) || !fmla.HasOp(wffP, fmla.Diamond) {
			continue
		}

		wffG = prf.GetWffG()

		maxOps = fmla.CountOps(wffG, fmla.Box) + fmla.CountOps(wffG, fmla.Diamond) + 1

		liSeq = genLineInfoSeq(prf)

		for ji1 = range liSeq {
			if maxOps < fmla.CountOps(ji1.wff, fmla.Box)+fmla.CountOps(ji1.wff, fmla.Diamond)+2 {
				continue
			}

			wff = fmla.NewUnaryWff(fmla.Diamond, ji1.wff)
			wff = fmla.NewUnaryWff(fmla.Box, wff)

			if fmla.HasSubformula(wffP, wff) {
				tot += ji1.prf.InsertNewLine(wff, pr.IntroB, 0, ji1.ln)
			} else if ji1.ln.GetRule() == pr.IntroB {
				continue
			}

			prfsI = ji1.prf.GetInnerProofsAtModalDistance(false, 1)

			for range prfsI {
				tot += ji1.prf.InsertNewLine(wff, pr.IntroB, 0, ji1.ln)

				break
			}
		}
	}

	return
}

var elimBFunc ndRuleFunc = func(drv *Deriver) (tot int) {
	var (
		liSeq iter.Seq[*lineInfo]
		ji1   *lineInfo
		wff   *fmla.Wff
	)

	liSeq = genLineInfoSeq(drv.Prf)

	for ji1 = range liSeq {
		if fmla.GetWffMop(ji1.wff) != fmla.Diamond {
			continue
		}

		if wff, _ = fmla.GetWffSubformulae(ji1.wff); fmla.GetWffMop(wff) != fmla.Box {
			continue
		}

		wff, _ = fmla.GetWffSubformulae(wff)

		tot += ji1.prf.InsertNewLine(wff, pr.ElimB, 0, ji1.ln)
	}

	return
}

func pushRules(drv *Deriver) (tot int) {
	if pr.IsRuleForSyntacticBreadth(pr.TopIntro, drv.SynB) { // At least propositional...
		if pr.NoInference < drv.InfS { // At least Implicational...
			tot += topIntroFunc(drv)                  // Zero premises.
			tot += reiterationFunc(drv)               // One premise.
			tot += toElimFunc(drv) + toIntroFunc(drv) // Two premises.
		}

		if pr.Implicational < drv.InfS { // At least Positive...
			tot += veeIntroFunc(drv) + iffElimFunc(drv)                         // One premise.
			tot += wedgeElimFunc(drv) + wedgeIntroFunc(drv) + iffIntroFunc(drv) // Two premises.
			tot += veeElimFunc(drv)                                             // Three premises.
		}

		if pr.Positive < drv.InfS { // At least Minimal...
			tot += botIntroFunc(drv) + negIntroFunc(drv) // Two premises.
		}

		if pr.Minimal < drv.InfS { // At least Intuitionistic...
			tot += botElimFunc(drv)
		}

		if pr.Intuitionistic < drv.InfS { // At least Classical...
			tot += negElimFunc(drv)
		}
	}

	if pr.IsRuleForSyntacticBreadth(pr.ForAllIntro, drv.SynB) { // At least quantificational...
		if pr.Implicational < drv.InfS { // At least Positive...
			tot += forAllElimFunc(drv) + existsIntroFunc(drv) // One premise.
			tot += forAllIntroFunc(drv)                       // Two premises.
			tot += existsElimFunc(drv)                        // Three premises.
		}
	}

	if pr.IsRuleForSyntacticBreadth(pr.EqualsIntro, drv.SynB) { // At least quantificational with identity...
		if pr.Implicational < drv.InfS { // At least Positive...
			tot += equalsIntroFunc(drv) // Zero premises.
			tot += equalsElimFunc(drv)  // Two premises.
		}
	}

	if pr.IsRuleForSyntacticBreadth(pr.BoxIntro, drv.SynB) { // At least modal...
		if pr.IsAllowedModality(pr.BoxIntro, drv.ModS) { // At least K...
			if pr.Implicational < drv.InfS { // At least Positive...
				tot += boxElimFunc(drv)     // One premise.
				tot += boxIntroFunc(drv)    // Two premises.
				tot += diamondElimFunc(drv) // Three premises.
			}

			if pr.Intuitionistic < drv.InfS { // At least Classical...
				tot += diamondIntroFunc(drv) // One premise.
			}
		}

		if pr.IsAllowedModality(pr.ElimD, drv.ModS) { // At least D...
			if pr.Implicational < drv.InfS { // At least Positive...
				tot += elimDFunc(drv) // One premise.
			}
		}

		if pr.IsAllowedModality(pr.IntroM, drv.ModS) { // At least M...
			if pr.Implicational < drv.InfS { // At least Positive...
				tot += elimMFunc(drv) + introMFunc(drv) // One premise.
			}
		}

		if pr.IsAllowedModality(pr.Intro4, drv.ModS) { // At least K...
			if pr.Implicational < drv.InfS { // At least Positive...
				tot += elim4Func(drv) + intro4Func(drv) // One premise.
			}
		}

		if pr.IsAllowedModality(pr.ElimB, drv.ModS) { // At least B...
			if pr.Implicational < drv.InfS { // At least Positive...
				tot += elimBFunc(drv) + introBFunc(drv) // One premise.
			}
		}
	}

	// Only run topElimFunc as a last resort.
	// if tot == 0 && pr.Implicational < drv.InfS { // At least positive.
	// 	tot += topElimFunc(drv)
	// }

	return
}
