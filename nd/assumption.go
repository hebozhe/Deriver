package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
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

func (drv *Deriver) pushAssumptions(wffG *fmla.Wff, prf *pr.Proof) (tot int) {
	var (
		wffA, wffB *fmla.Wff
		prfI       *pr.Proof
		mop        fmla.Symbol
		ok         bool
		pc         fmla.Predicate
		ln0        *pr.Line
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

					tot += drv.pushAssumptions(wffA, prf)
				}
			}
		}
	case fmla.Wedge: // ⊢ A∧B
		switch drv.InfS {
		case pr.Classical:
			// ¬¬A, ¬¬B ⊢ A, B ⊢ A∧B
			wffA, wffB = fmla.GetWffSubformulae(wffG)
			wffA, wffB = fmla.FillTemplate("¬¬(?)", wffA), fmla.FillTemplate("¬¬(?)", wffB)

			tot += drv.pushAssumptions(wffA, prf) + drv.pushAssumptions(wffB, prf)

			fallthrough
		case pr.Intuitionistic:
			// [A ... ⊥], [¬A ... ⊥] ⊢ ¬A, ¬¬A ⊢ ⊥ ⊢ A∧B
			// [B ... ⊥], [¬B ... ⊥] ⊢ ¬B, ¬¬B ⊢ ⊥ ⊢ A∧B
			wffA, wffB = fmla.GetWffSubformulae(wffG)

			wffA, wffB = fmla.FillTemplate("¬(?)", wffA), fmla.FillTemplate("¬(?)", wffB)

			tot += drv.pushAssumptions(wffA, prf) + drv.pushAssumptions(wffB, prf)

			wffA, wffB = fmla.FillTemplate("¬(?)", wffA), fmla.FillTemplate("¬(?)", wffB)

			tot += drv.pushAssumptions(wffA, prf) + drv.pushAssumptions(wffB, prf)

			fallthrough
		case pr.Minimal, pr.Positive:
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
			}

			// ¬¬A ⊢ A ⊢ A∨B
			// ¬¬B ⊢ B ⊢ A∨B
			wffA, wffB = fmla.GetWffSubformulae(wffG)
			wffA, wffB = fmla.FillTemplate("¬¬(?)", wffA), fmla.FillTemplate("¬¬(?)", wffB)

			tot += drv.pushAssumptions(wffA, prf) + drv.pushAssumptions(wffB, prf)

			fallthrough
		case pr.Intuitionistic, pr.Minimal, pr.Positive:
			// A ⊢ A∨B
			// B ⊢ A∨B
			wffA, wffB = fmla.GetWffSubformulae(wffG)

			tot += drv.pushAssumptions(wffA, prf) + drv.pushAssumptions(wffB, prf)
		}
	case fmla.To: // ⊢ A→B
		switch drv.InfS {
		case pr.Classical:
			// [¬(A→B), ¬¬A, ¬B, ... ⊥] ⊢ ¬¬(A→B) ⊢ A→B
			// wffA, wffB = fmla.NewUnaryWff(fmla.Neg, wffG), fmla.NewAtomicWff(fmla.Bot)

			// if prfI, ok = makeNewInnerProof(wffA, wffB, prf, pr.NegIntro); ok {
			// 	tot += prf.InsertInnerProofs(prfI)

			// 	// Accelerate the proof with [¬(A→B), ... ] ⊢ [¬(A→B), ¬¬A, ¬B... ].
			// 	wffA, wffB = fmla.GetWffSubformulae(wffG)
			// 	wffA, wffB = fmla.FillTemplate("¬¬(?)", wffA), fmla.NewUnaryWff(fmla.Neg, wffB)

			// 	tot += drv.pushAssumptions(wffA, prfI) + drv.pushAssumptions(wffB, prfI)

			// 	ln0 = prfI.GetLineAtIndex(0)

			// 	_ = ln0.SetExtended(true)
			// }

			fallthrough
		case pr.Intuitionistic:
			// [A ... ⊥] ⊢ ¬A ⊢ A→B
			wffA, _ = fmla.GetWffSubformulae(wffG)
			wffA = fmla.NewUnaryWff(fmla.Neg, wffA)

			tot += drv.pushAssumptions(wffA, prf)

			fallthrough
		case pr.Minimal:
			// If ¬B, then [A ... ⊥] ⊢ ¬A ⊢ A→¬B
			wffA, wffB = fmla.GetWffSubformulae(wffG)

			if fmla.GetWffMop(wffB) == fmla.Neg {
				wffA = fmla.NewUnaryWff(fmla.Neg, wffA)

				tot += drv.pushAssumptions(wffA, prf)
			}

			fallthrough
		case pr.Positive, pr.Implicational:
			// [A ... B] ⊢ A→B
			wffA, wffB = fmla.GetWffSubformulae(wffG)

			if prfI, ok = makeNewInnerProof(wffA, wffB, prf, pr.ToIntro); ok {
				tot += prf.InsertInnerProofs(prfI) + drv.pushAssumptions(wffB, prfI)
			}
		}
	case fmla.Iff: // ⊢ A↔B
		switch drv.InfS {
		case pr.Classical, pr.Intuitionistic, pr.Minimal, pr.Positive:
			// [A ... B], [B ... A] ⊢ A→B, B→A ⊢ A↔B
			wffA, wffB = fmla.GetWffSubformulae(wffG)

			if prfI, ok = makeNewInnerProof(wffA, wffB, prf, pr.ToIntro); ok {
				tot += prf.InsertInnerProofs(prfI) + drv.pushAssumptions(wffB, prfI)
			}

			if prfI, ok = makeNewInnerProof(wffB, wffA, prf, pr.ToIntro); ok {
				tot += prf.InsertInnerProofs(prfI) + drv.pushAssumptions(wffA, prfI)
			}
		}
	case fmla.ForAll: // ⊢ ∀[x|X]A
		// var (
		// 	pv fmla.Predicate
		// 	av fmla.Argument
		// )

		switch drv.InfS {
		case pr.Classical, pr.Intuitionistic, pr.Minimal, pr.Positive:
			// [⊤ ... A(t/x|T/X)] ⊢ ∀[x|X]A
			wffA = fmla.NewAtomicWff(fmla.Top)

			if prfI, ok = makeNewInnerProof(wffA, wffG, prf, pr.ForAllIntro); ok {
				wffB = prfI.GetWffG() // makeNewInnerProof freshly instantiates for you.

				tot += prf.InsertInnerProofs(prfI) + drv.pushAssumptions(wffB, prfI)
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
			// ¬¬∃[x|X]A ⊢ ∃[x|X]A
			wffA = fmla.FillTemplateWithLocales("¬¬(?)", wffG, "!")

			tot += drv.pushAssumptions(wffA, prf)

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
			if pr.IsAllowedModality(pr.DiamondElim, drv.ModS) {
				wffA = fmla.FillTemplateWithLocales("¬¬□(?)", wffG, "L!")

				tot += drv.pushAssumptions(wffA, prf)
			}

			fallthrough
		case pr.Intuitionistic, pr.Minimal, pr.Positive:
			if pr.IsAllowedModality(pr.BoxIntro, drv.ModS) {
				// [⊤ ... A] ⊢ □A
				wffA, wffB = fmla.NewAtomicWff(fmla.Top), fmla.RetrieveSubformula(wffG, "L!")

				if prfI, ok = makeNewInnerProof(wffA, wffB, prf, pr.BoxIntro); ok {
					tot += prf.InsertInnerProofs(prfI) + drv.pushAssumptions(wffB, prfI)
				}
			}
		}
	case fmla.Diamond: // ⊢ ◇A
		switch drv.InfS {
		case pr.Classical:
			if pr.IsAllowedModality(pr.DiamondIntro, drv.ModS) {
				// ¬□¬A ⊢ ◇A

				wffA = fmla.FillTemplateWithLocales("¬□¬(?)", wffG, "L!")

				tot += drv.pushAssumptions(wffA, prf)
			}

			fallthrough
		case pr.Intuitionistic, pr.Minimal, pr.Positive:
			if pr.IsAllowedModality(pr.ElimD, drv.ModS) {
				// □A ⊢ ◇A
				wffA = fmla.FillTemplateWithLocales("□(?)", wffG, "L!")

				tot += drv.pushAssumptions(wffA, prf)
			}

			if pr.IsAllowedModality(pr.IntroM, drv.ModS) {
				// A ⊢ ◇A
				wffA = fmla.RetrieveSubformula(wffG, "L!")

				tot += drv.pushAssumptions(wffA, prf)
			}
		}
	}

	return
}
