package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
)

func distributeWff(wff *fmla.WffTree, infS pr.InfStrength, _ pr.ModStrength) (wffD *fmla.WffTree) {
	var (
		swffs                    []*fmla.WffTree
		tmp                      string
		mop                      fmla.Symbol
		dex                      int
		swff, subLL, subLR, wffT *fmla.WffTree
		// pv                       fmla.Predicate
		// av                       fmla.Argument
	)

DISTRIBUTEWFF_RESTART:
	swffs = fmla.GetAllSubformulae(wff)

	for dex, swff = range swffs {
		mop = fmla.GetWffMop(swff)

		switch mop {
		case fmla.Neg: // ~(...)
			mop = fmla.GetWffMop(swffs[dex+1])

			subLL, subLR = fmla.GetWffSubformulae(swffs[dex+1])

			switch mop {
			case fmla.Wedge: // ¬(A∧B) :: (A→¬B)∧(B→¬A)
				if pr.Positive < infS { // At least Minimal...
					tmp = "((?)→¬(?))∧((?)→¬(?))"

					wffT = fmla.FillTemplate(tmp, subLL, subLR, subLR, subLL)

					wff = fmla.ReplaceWff(wff, swff, wffT)

					goto DISTRIBUTEWFF_RESTART
				}
			case fmla.Vee: // ¬(A∨B) :: ¬A∧¬B
				if pr.Positive < infS { // At least Minimal...
					tmp = "¬(?)∧¬(?)"

					wffT = fmla.FillTemplate(tmp, subLL, subLR)

					wff = fmla.ReplaceWff(wff, swff, wffT)

					goto DISTRIBUTEWFF_RESTART
				}
			case fmla.To: // ¬(A→B) :: ¬¬A∧¬B
				if pr.Minimal < infS { // At least Intuitionistic...
					tmp = "¬¬(?)∧¬(?)"

					wffT = fmla.FillTemplate(tmp, subLL, subLR)

					wff = fmla.ReplaceWff(wff, swff, wffT)

					goto DISTRIBUTEWFF_RESTART
				} else if pr.Positive < infS { // At least Minimal...
					tmp = "⊤∧¬(?)"

					wffT = fmla.FillTemplate(tmp, subLL)

					wff = fmla.ReplaceWff(wff, swff, wffT)

					goto DISTRIBUTEWFF_RESTART
				}
			case fmla.Iff: // ¬(A↔B) :: ¬((A→B)∧(B→A))
				if pr.Positive < infS { // At least Minimal...
					tmp = "¬((?)→¬(?))∧((?)→¬(?))"

					wffT = fmla.FillTemplate(tmp, subLL, subLR, subLR, subLL)

					wff = fmla.ReplaceWff(wff, swff, wffT)

					goto DISTRIBUTEWFF_RESTART
				}
			}
		case fmla.ForAll: // ∀x(...) or ∀X(...)
			// mop = fmla.GetWffMop(swffs[dex+1])

			// subLL, subLR = fmla.GetWffSubformulae(swffs[dex+1])

			// switch mop {
			// case fmla.Wedge: // ∀(x|X)(A∧B) :: ∀(x|X)A∧∀(x|X)B
			// 	if pr.Implicational < infS { // At least Positive...
			// 		if pv, av = fmla.GetWffVars(swffs[dex]); pv != 0 {
			// 			tmp = fmt.Sprintf("∀%c(?)∧∀%c(?)", pv, pv)
			// 		} else if av != 0 {
			// 			tmp = fmt.Sprintf("∀%c(?)∧∀%c(?)", av, av)
			// 		}

			// 		wffT = fmla.FillTemplate(tmp, subLL, subLR)

			// 		wff = fmla.ReplaceWff(wff, swff, wffT)

			// 		goto DISTRIBUTEWFF_RESTART
			// 	}
			// case fmla.Vee: // ∀(x|X)(A∨B) :: ∀(x|X)A∨∀(x|X)B
			// 	if pr.Implicational < infS { // At least Positive...
			// 		if pv, av = fmla.GetWffVars(swffs[dex]); pv != 0 {
			// 			tmp = fmt.Sprintf("∀%c(?)∨∀%c(?)", pv, pv)
			// 		} else if av != 0 {
			// 			tmp = fmt.Sprintf("∀%c(?)∨∀%c(?)", av, av)
			// 		}

			// 		wffT = fmla.FillTemplate(tmp, subLL, subLR)

			// 		wff = fmla.ReplaceWff(wff, swff, wffT)

			// 		goto DISTRIBUTEWFF_RESTART
			// 	}
			// case fmla.To: // ∀(x|X)(A→B) :: (∀(x|X)A→∀(x|X)B)∧(∃(x|X)A→∃(x|X)B)
			// 	if pr.Implicational < infS { // At least Positive...
			// 		if pv, av = fmla.GetWffVars(swffs[dex]); pv != 0 {
			// 			tmp = fmt.Sprintf("(∀%c(?)→∀%c(?))∧(∃%c(?)→∃%c(?))", pv, pv, pv, pv)
			// 		} else if av != 0 {
			// 			tmp = fmt.Sprintf("(∀%c(?)→∀%c(?))∧(∃%c(?)→∃%c(?))", av, av, av, av)
			// 		}

			// 		wffT = fmla.FillTemplate(tmp, subLL, subLR, subLL, subLR)

			// 		wff = fmla.ReplaceWff(wff, swff, wffT)

			// 		goto DISTRIBUTEWFF_RESTART
			// 	}
			// case fmla.Iff: // ∀(x|X)(A↔B) :: ∀(x|X)((A→B)∧(B→A))
			// 	if pr.Implicational < infS { // At least Positive...
			// 		if pv, av = fmla.GetWffVars(swffs[dex]); pv != 0 {
			// 			tmp = fmt.Sprintf("∀%c(((?)→(?))∧((?)→(?)))", pv)
			// 		} else if av != 0 {
			// 			tmp = fmt.Sprintf("∀%c(((?)→(?))∧((?)→(?)))", av)
			// 		}

			// 		wffT = fmla.FillTemplate(tmp, subLL, subLR, subLR, subLL)

			// 		wff = fmla.ReplaceWff(wff, swff, wffT)

			// 		goto DISTRIBUTEWFF_RESTART
			// 	}
			// }
		case fmla.Exists: // ∃x(...) or ∃X(...)
			// mop = fmla.GetWffMop(swffs[dex+1])

			// subLL, subLR = fmla.GetWffSubformulae(swffs[dex+1])

			// switch mop {
			// case fmla.Wedge: // ∃(x|X)(A∧B) :: ∃(x|X)A∧∃(x|X)B
			// 	if pr.Implicational < infS { // At least Positive...
			// 		if pv, av = fmla.GetWffVars(swffs[dex]); pv != 0 {
			// 			tmp = fmt.Sprintf("∃%c(?)∧∃%c(?)", pv, pv)
			// 		} else if av != 0 {
			// 			tmp = fmt.Sprintf("∃%c(?)∧∃%c(?)", av, av)
			// 		}

			// 		wffT = fmla.FillTemplate(tmp, subLL, subLR)

			// 		wff = fmla.ReplaceWff(wff, swff, wffT)

			// 		goto DISTRIBUTEWFF_RESTART
			// 	}
			// case fmla.Vee: // ∃(x|X)(A∨B) :: ∃(x|X)A∨∃(x|X)B
			// 	if pr.Intuitionistic < infS { // At least Classical...
			// 		if pv, av = fmla.GetWffVars(swffs[dex]); pv != 0 {
			// 			tmp = fmt.Sprintf("∃%c(?)∨∃%c(?)", pv, pv)
			// 		} else if av != 0 {
			// 			tmp = fmt.Sprintf("∃%c(?)∨∃%c(?)", av, av)
			// 		}

			// 		wffT = fmla.FillTemplate(tmp, subLL, subLR)

			// 		wff = fmla.ReplaceWff(wff, swff, wffT)

			// 		goto DISTRIBUTEWFF_RESTART
			// 	}
			// case fmla.To: // ∃(x|X)(A↔B) :: ∀(x|X)A→∃(x|X)B
			// 	if pr.Implicational < infS { // At least Positive...
			// 		if pv, av = fmla.GetWffVars(swffs[dex]); pv != 0 {
			// 			tmp = fmt.Sprintf("∀%c(?)→∃%c(?)", pv, pv)
			// 		} else if av != 0 {
			// 			tmp = fmt.Sprintf("∀%c(?)→∃%c(?)", av, av)
			// 		}

			// 		wffT = fmla.FillTemplate(tmp, subLL, subLR)

			// 		wff = fmla.ReplaceWff(wff, swff, wffT)

			// 		goto DISTRIBUTEWFF_RESTART
			// 	}
			// case fmla.Iff: // ∃(x|X)(A↔B) :: ∃(x|X)((A→B)∧(B→A))
			// 	if pr.Implicational < infS { // At least Positive...
			// 		if pv, av = fmla.GetWffVars(swffs[dex]); pv != 0 {
			// 			tmp = fmt.Sprintf("∃%c(((?)→(?))∧((?)→(?)))", pv)
			// 		} else if av != 0 {
			// 			tmp = fmt.Sprintf("∃%c(((?)→(?))∧((?)→(?)))", av)
			// 		}

			// 		wffT = fmla.FillTemplate(tmp, subLL, subLR, subLR, subLL)

			// 		wff = fmla.ReplaceWff(wff, swff, wffT)

			// 		goto DISTRIBUTEWFF_RESTART
			// 	}
			// }
		case fmla.Box: // [](...)
			mop = fmla.GetWffMop(swffs[dex+1])

			subLL, subLR = fmla.GetWffSubformulae(swffs[dex+1])

			switch mop {
			case fmla.Wedge: // □(A∧B) :: □A∧□B
				if pr.Implicational < infS { // At least Positive...
					tmp = "□(?)∧□(?)"

					wffT = fmla.FillTemplate(tmp, subLL, subLR)

					wff = fmla.ReplaceWff(wff, swff, wffT)

					goto DISTRIBUTEWFF_RESTART
				}
			case fmla.Vee: // □(A∨B) :: □A∨□B
				if pr.Implicational < infS { // At least Positive...
					tmp = "□(?)∨□(?)"

					wffT = fmla.FillTemplate(tmp, subLL, subLR)

					wff = fmla.ReplaceWff(wff, swff, wffT)

					goto DISTRIBUTEWFF_RESTART
				}
			case fmla.To: // □(A→B) :: (□A→□B)∧(◇A→◇B)
				if pr.Implicational < infS { // At least Positive...
					tmp = "(□(?)→□(?))∧(◇(?)→◇(?))"

					wffT = fmla.FillTemplate(tmp, subLL, subLR, subLR, subLL)

					wff = fmla.ReplaceWff(wff, swff, wffT)

					goto DISTRIBUTEWFF_RESTART
				}
			case fmla.Iff: // □(A↔B) :: (□A↔□B)∧(◇A↔◇B)
				if pr.Implicational < infS { // At least Positive...
					tmp = "(□(?)↔□(?))∧(◇(?)↔◇(?))"

					wffT = fmla.FillTemplate(tmp, subLL, subLR, subLR, subLL)

					wff = fmla.ReplaceWff(wff, swff, wffT)

					goto DISTRIBUTEWFF_RESTART
				}
			}
		case fmla.Diamond: // <>(...)
			mop = fmla.GetWffMop(swffs[dex+1])

			subLL, subLR = fmla.GetWffSubformulae(swffs[dex+1])

			switch mop {
			case fmla.Wedge: // ◇(A∧B) :: ◇A∧◇B
				if pr.Implicational < infS { // At least Positive...
					tmp = "◇(?)∧◇(?)"

					wffT = fmla.FillTemplate(tmp, subLL, subLR)

					wff = fmla.ReplaceWff(wff, swff, wffT)

					goto DISTRIBUTEWFF_RESTART
				}
			case fmla.Vee: // ◇(A∨B) :: ◇A∨◇B
				if pr.Intuitionistic < infS { // At least Classical...
					tmp = "◇(?)∨◇(?)"

					wffT = fmla.FillTemplate(tmp, subLL, subLR)

					wff = fmla.ReplaceWff(wff, swff, wffT)

					goto DISTRIBUTEWFF_RESTART
				}
			case fmla.To: // ◇(A→B) :: □A→◇B
				if pr.Implicational < infS { // At least Positive...
					tmp = "□(?)→◇(?)"

					wffT = fmla.FillTemplate(tmp, subLL, subLR)

					wff = fmla.ReplaceWff(wff, swff, wffT)

					goto DISTRIBUTEWFF_RESTART
				}
			case fmla.Iff: // ◇(A↔B) :: (□A→◇B)∧(□A→◇B)
				if pr.Implicational < infS { // At least Positive...
					tmp = "(□(?)→◇(?))∧(□(?)→◇(?))"

					wffT = fmla.FillTemplate(tmp, subLL, subLR, subLR, subLL)

					wff = fmla.ReplaceWff(wff, swff, wffT)

					goto DISTRIBUTEWFF_RESTART
				}
			}
		}
	}

	wffD = wff

	return
}
