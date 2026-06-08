package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
	"fmt"
)

func makeNewInnerProof(wffA, wffG *fmla.Wff, prf *pr.Proof, purp pr.NDRule, js ...*pr.Line) (prfI *pr.Proof, ok bool) {
	var (
		ln0    *pr.Line
		pv, pc fmla.Predicate
		av, ac fmla.Argument
	)

	ok = true

	switch purp {
	case pr.ForAllIntro:
		if pv, av = fmla.GetWffVars(wffG); pv != 0 {
			if pc, ok = prf.GetFreshPredicate(); ok {
				wffG = fmla.Instantiate(wffG, pc, 0)
			}
		} else if av != 0 {
			if ac, ok = prf.GetFreshArgument(); ok {
				wffG = fmla.Instantiate(wffG, 0, ac)
			}
		}
	case pr.ExistsElim:
		if pv, av = fmla.GetWffVars(wffA); pv != 0 {
			if pc, ok = prf.GetFreshPredicate(); ok {
				wffA = fmla.Instantiate(wffA, pc, 0)
			}
		} else if av != 0 {
			if ac, ok = prf.GetFreshArgument(); ok {
				wffA = fmla.Instantiate(wffA, 0, ac)
			}
		}
	}

	if ok {
		ln0 = prf.NewLine(wffA, pr.Assumption, purp, js...)

		prfI = prf.NewInnerProof(wffG, purp, ln0)
	}

	switch purp {
	case pr.ForAllIntro:
		if pv != 0 {
			ok = prfI.SetQLInnerProofPredicates(pc, pv) && !prfI.IsRedundant()
		} else if av != 0 {
			ok = prfI.SetQLInnerProofArguments(ac, av) && !prfI.IsRedundant()
		}
	case pr.ExistsElim:
		if pv != 0 {
			ok = prfI.SetQLInnerProofPredicates(pc, pv) && !prfI.IsRedundant()
		} else if av != 0 {
			ok = prfI.SetQLInnerProofArguments(ac, av) && !prfI.IsRedundant()
		}
	default:
		ok = !prfI.IsRedundant()
	}

	return
}

func (drv *Deriver) getElimGoalsFromNewPrf(prf *pr.Proof) (wffsE []*fmla.Wff) {
	var (
		ln0                   *pr.Line
		wff, wffA, wffB, wffG *fmla.Wff
		mop                   fmla.Symbol
		prfI                  *pr.Proof
		ok                    bool
	)

	ln0 = prf.GetLineAtIndex(0)

	wff, wffG = ln0.GetWff(), prf.GetWffG()

	mop = fmla.GetWffMop(wff)

	switch mop {
	case fmla.Neg:
		if pr.Positive < drv.InfS { // At least MPL...
			wffA, _ = fmla.GetWffSubformulae(wff)

			wffsE = append(wffsE, wffA)
		}
	case fmla.Vee:
		if pr.Implicational < drv.InfS { // At least PPL...
			wffA, wffB = fmla.GetWffSubformulae(wff)

			wffA, wffB = fmla.NewBinaryWff(fmla.To, wffA, wffG), fmla.NewBinaryWff(fmla.To, wffB, wffG)

			wffsE = append(wffsE, wffA, wffB)
		}
	case fmla.Wedge:
		if pr.Implicational < drv.InfS { // At least PPL...
			wffA, wffB = fmla.GetWffSubformulae(wff)

			wffsE = append(wffsE, wffA, wffB)
		}
	case fmla.To:
		if pr.NoInference < drv.InfS { // At least TPL...
			wffA, _ = fmla.GetWffSubformulae(wff)

			wffsE = append(wffsE, wffA)
		}
	case fmla.Iff:
		if pr.Implicational < drv.InfS { // At least PPL...
			wffA, wffB = fmla.GetWffSubformulae(wff)

			wffsE = append(wffsE, wffA, wffB)
		}
	case fmla.ForAll: // ∀E is a one-premise rule. Skip!
	case fmla.Exists:
		if pr.Implicational < drv.InfS { // At least P[12]QL...
			if prfI, ok = makeNewInnerProof(wff, wffG, prf, pr.ExistsElim, ln0); ok {
				_ = prf.InsertInnerProofs(prfI) + drv.pushAssumptions(wffG, prfI)
			}
		}
	case fmla.Box: // What to do here?
	case fmla.Diamond:
		var (
			prfsO []*pr.Proof
			prfO  *pr.Proof
			bot   *fmla.Wff
		)

		prfsO = prf.GetOuterProofsAtModalDistance(true, 0)

		if pr.Implicational < drv.InfS && pr.HasModality(drv.ModS, pr.ModalK) { // At least PPL+K...
			wffA = fmla.RetrieveSubformula(wff, "L!")

			for _, prfO = range prfsO {
				if wffB = prfO.GetWffG(); fmla.GetWffMop(wffB) != fmla.Diamond {
					continue
				}

				wffB = fmla.RetrieveSubformula(wffB, "L!")

				if prfI, ok = makeNewInnerProof(wffA, wffB, prf, pr.DiamondElim, ln0); ok {
					_ = prf.InsertInnerProofs(prfI) + drv.pushAssumptions(wffB, prfI)
				}
			}
		}

		if pr.Positive < drv.InfS && pr.HasModality(drv.ModS, pr.ModalK) { // At least MPL+K...
			wffA, bot = fmla.RetrieveSubformula(wff, "L!"), fmla.NewAtomicWff(fmla.Bot)

			for _, prfO = range prfsO {
				if wffB = prfO.GetWffG(); !fmla.IsIdentical(wffB, bot) {
					continue
				}

				if prfI, ok = makeNewInnerProof(wffA, wffB, prf, pr.DiamondElim, ln0); ok {
					_ = prf.InsertInnerProofs(prfI)

					break
				}
			}
		}
	default:
	}

	return
}

func (drv *Deriver) pushAssumptions(wffG *fmla.Wff, prf *pr.Proof) (tot int) {
	var (
		wffA, wffB, wffE *fmla.Wff
		prfI             *pr.Proof
		mop              fmla.Symbol
		ok               bool
		pc               fmla.Predicate
		ln0              *pr.Line
	)

	mop = fmla.GetWffMop(wffG)

	switch mop {
	case fmla.NoSymbol: // ⊢ A
		pc, _, _ = fmla.GetWffPredAndArgs(wffG)

		switch pc {
		case fmla.Top, fmla.Bot, fmla.Equals:
		default:
			switch drv.InfS {
			case pr.Classical:
				// [¬A ... ⊥] ⊢ ¬¬A ⊢ A
				wffA, wffB = fmla.NewUnaryWff(fmla.Neg, wffG), fmla.NewAtomicWff(fmla.Bot)

				if prfI, ok = makeNewInnerProof(wffA, wffB, prf, pr.NegIntro); ok {
					tot += prf.InsertInnerProofs(prfI)
				}
			}
		}
	case fmla.Neg: // ⊢ ¬A
		switch drv.InfS {
		case pr.Classical, pr.Intuitionistic, pr.Minimal:
			// [A ... ⊥] ⊢ ¬A
			// If [ ... ] ⊢ A, then [¬A, [ ... ] ... ⊥] ⊢ [¬A, A, ⊥] ¬¬A
			wffA, wffB = fmla.RetrieveSubformula(wffG, "L!"), fmla.NewAtomicWff(fmla.Bot)

			if prfI, ok = makeNewInnerProof(wffA, wffB, prf, pr.NegIntro); ok {
				tot += prf.InsertInnerProofs(prfI)

				if fmla.GetWffMop(wffA) == fmla.Neg {
					wffA = fmla.RetrieveSubformula(wffA, "L!")

					tot += drv.pushAssumptions(wffA, prfI)
				}
			}
		}
	case fmla.Wedge: // ⊢ A∧B
		switch drv.InfS {
		case pr.Classical, pr.Intuitionistic, pr.Minimal, pr.Positive:
			// A, B ⊢ A∧B
			wffA, wffB = fmla.GetWffSubformulae(wffG)

			tot += drv.pushAssumptions(wffA, prf) + drv.pushAssumptions(wffB, prf)
		}
	case fmla.Vee: // ⊢ A∨B
		switch drv.InfS {
		case pr.Classical:
			// [¬(A∨B), ... ⊥] ⊢ ¬¬(A∨B) ⊢ A∨B
			wffA, wffB = fmla.NewUnaryWff(fmla.Neg, wffG), fmla.NewAtomicWff(fmla.Bot)

			if prfI, ok = makeNewInnerProof(wffA, wffB, prf, pr.NegIntro); ok {
				tot += prf.InsertInnerProofs(prfI)

				// Accelerate the proof with [¬(A∨B), ... ] ⊢ [¬(A∨B), ¬A, ¬B... ].
				wffA, wffB = fmla.GetWffSubformulae(wffG)
				wffA, wffB = fmla.NewUnaryWff(fmla.Neg, wffA), fmla.NewUnaryWff(fmla.Neg, wffB)

				tot += drv.pushAssumptions(wffA, prfI) + drv.pushAssumptions(wffB, prfI)

				ln0 = prfI.GetLineAtIndex(0)

				_ = ln0.SetExtended(true)

				for _, wffE = range drv.getElimGoalsFromNewPrf(prfI) {
					tot += drv.pushAssumptions(wffE, prfI)
				}
			}

			fallthrough
		case pr.Intuitionistic, pr.Minimal, pr.Positive:
			// A ⊢ A∨B
			// B ⊢ A∨B
			wffA, wffB = fmla.GetWffSubformulae(wffG)

			tot += drv.pushAssumptions(wffA, prf) + drv.pushAssumptions(wffB, prf)
		}
	case fmla.To: // ⊢ A→B
		switch drv.InfS {
		case pr.Classical, pr.Intuitionistic, pr.Minimal, pr.Positive, pr.Implicational:
			// [A ... B] ⊢ A→B
			wffA, wffB = fmla.GetWffSubformulae(wffG)

			if prfI, ok = makeNewInnerProof(wffA, wffB, prf, pr.ToIntro); ok {
				tot += prf.InsertInnerProofs(prfI) + drv.pushAssumptions(wffB, prfI)

				for _, wffE = range drv.getElimGoalsFromNewPrf(prfI) {
					tot += drv.pushAssumptions(wffE, prfI)
				}
			}
		}
	case fmla.Iff: // ⊢ A↔B
		switch drv.InfS {
		case pr.Classical, pr.Intuitionistic, pr.Minimal, pr.Positive:
			// [A ... B], [B ... A] ⊢ A→B, B→A ⊢ A↔B
			wffA, wffB = fmla.GetWffSubformulae(wffG)

			if prfI, ok = makeNewInnerProof(wffA, wffB, prf, pr.ToIntro); ok {
				tot += prf.InsertInnerProofs(prfI) + drv.pushAssumptions(wffB, prfI)

				for _, wffE = range drv.getElimGoalsFromNewPrf(prfI) {
					tot += drv.pushAssumptions(wffE, prfI)
				}
			}

			if prfI, ok = makeNewInnerProof(wffB, wffA, prf, pr.ToIntro); ok {
				tot += prf.InsertInnerProofs(prfI) + drv.pushAssumptions(wffA, prfI)

				for _, wffE = range drv.getElimGoalsFromNewPrf(prfI) {
					tot += drv.pushAssumptions(wffE, prfI)
				}
			}
		}
	case fmla.ForAll: // ⊢ ∀[x|X]A
		switch drv.InfS {
		case pr.Classical, pr.Intuitionistic, pr.Minimal, pr.Positive:
			// [⊤ ... A(t/x|T/X)] ⊢ ∀[x|X]A
			wffA = fmla.NewAtomicWff(fmla.Top)

			if prfI, ok = makeNewInnerProof(wffA, wffG, prf, pr.ForAllIntro); ok {
				wffB = prfI.GetWffG() // makeNewInnerProof freshly instantiates for you.

				tot += prf.InsertInnerProofs(prfI) + drv.pushAssumptions(wffB, prfI)

				for _, wffE = range drv.getElimGoalsFromNewPrf(prfI) {
					tot += drv.pushAssumptions(wffE, prfI)
				}
			}
		}
	case fmla.Exists: // ⊢ ∃[x|X]A
		var (
			pv, pc fmla.Predicate
			av, ac fmla.Argument
			pcs    []fmla.Predicate
			acs    []fmla.Argument
			lenC   int
		)

		switch drv.InfS {
		case pr.Classical:
			// [¬∃[x|X]A ... ⊥] ⊢ ¬¬∃[x|X]A ⊢ ∃[x|X]A
			var (
				pv  fmla.Predicate
				av  fmla.Argument
				tmp string
			)

			wffA, wffB = fmla.NewUnaryWff(fmla.Neg, wffG), fmla.NewAtomicWff(fmla.Bot)

			if prfI, ok = makeNewInnerProof(wffA, wffB, prf, pr.NegIntro); ok {
				tot += prf.InsertInnerProofs(prfI)

				if pv, av = fmla.GetWffVars(wffG); pv != 0 {
					tmp = fmt.Sprintf("∀%c¬(?)", pv)
				} else if av != 0 {
					tmp = fmt.Sprintf("∀%c¬(?)", av)
				}

				wffA = fmla.FillTemplateWithLocales(tmp, wffG, "L!")

				tot += drv.pushAssumptions(wffA, prfI)
			}

			fallthrough
		case pr.Intuitionistic, pr.Minimal, pr.Positive:
			// A(t/x|T/X) ⊢ ∃[x|X]A
			if pv, av = fmla.GetWffVars(wffG); pv != 0 {
				pcs = prf.GetUsedPredicates()

				if lenC = len(pcs); lenC == 0 {
					if pc, ok = prf.GetFreshPredicate(); ok {
						wffA = fmla.Instantiate(wffG, pc, 0)

						tot += drv.pushAssumptions(wffA, prf)
					}
				} else {
					for _, pc = range pcs {
						wffA = fmla.Instantiate(wffG, pc, 0)

						tot += drv.pushAssumptions(wffA, prf)
					}
				}

			} else if av != 0 {
				acs = prf.GetUsedArguments()

				if lenC = len(acs); lenC == 0 {
					if ac, ok = prf.GetFreshArgument(); ok {
						wffA = fmla.Instantiate(wffG, 0, ac)

						tot += drv.pushAssumptions(wffA, prf)
					}
				} else {
					for _, ac = range acs {
						wffA = fmla.Instantiate(wffG, 0, ac)

						tot += drv.pushAssumptions(wffA, prf)
					}
				}
			}
		}
	case fmla.Box: // ⊢ □A
		switch drv.InfS {
		case pr.Classical:
			wffA = fmla.FillTemplateWithLocales("¬¬□(?)", wffG, "L!")

			tot += drv.pushAssumptions(wffA, prf)

			fallthrough
		case pr.Intuitionistic, pr.Minimal, pr.Positive:
			if pr.HasModality(drv.ModS, pr.ModalK) {
				// [⊤ ... A] ⊢ □A
				wffA, wffB = fmla.NewAtomicWff(fmla.Top), fmla.RetrieveSubformula(wffG, "L!")

				if prfI, ok = makeNewInnerProof(wffA, wffB, prf, pr.BoxIntro); ok {
					tot += prf.InsertInnerProofs(prfI) + drv.pushAssumptions(wffB, prfI)

					for _, wffE = range drv.getElimGoalsFromNewPrf(prfI) {
						tot += drv.pushAssumptions(wffE, prfI)
					}
				}
			}
		}
	case fmla.Diamond: // ⊢ ◇A
		switch drv.InfS {
		case pr.Classical:
			if pr.HasModality(drv.ModS, pr.ModalK) {
				// ¬□¬A ⊢ ◇A

				wffA = fmla.FillTemplateWithLocales("¬□¬(?)", wffG, "L!")

				tot += drv.pushAssumptions(wffA, prf)
			}

			if pr.HasModality(drv.ModS, pr.ModalD) {
				// ¬¬□A ⊢ □A ⊢ ◇A
				wffA = fmla.FillTemplateWithLocales("¬¬□(?)", wffG, "L!")

				tot += drv.pushAssumptions(wffA, prf)
			}

			if pr.HasModality(drv.ModS, pr.ModalM) {
				// ¬¬A ⊢ A ⊢ ◇A
				wffA = fmla.FillTemplateWithLocales("¬¬(?)", wffG, "L!")

				tot += drv.pushAssumptions(wffA, prf)
			}

			fallthrough
		case pr.Intuitionistic, pr.Minimal, pr.Positive:
			if pr.HasModality(drv.ModS, pr.ModalD) {
				// □A ⊢ ◇A
				wffA = fmla.FillTemplateWithLocales("□(?)", wffG, "L!")

				tot += drv.pushAssumptions(wffA, prf)
			}

			if pr.HasModality(drv.ModS, pr.ModalM) {
				// A ⊢ ◇A
				wffA = fmla.RetrieveSubformula(wffG, "L!")

				tot += drv.pushAssumptions(wffA, prf)
			}
		}
	}

	return
}
