package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
)

func goalAssume(prfG *pr.Prf, wffG *fmla.Wff, inf pr.InfStrength, mod pr.ModStrength) (tot int) {
	var (
		subL, subR, newA, newG *fmla.Wff
		prfI                   *pr.Prf
		pms                    pr.PrfMutStatus
	)

	switch wffG.Mop() {
	case fmla.NoSym:
		switch wffG.Pred() {
		case fmla.Top: // G is ⊤.
			if pr.RuleFitsStrengths(pr.TopI, inf, mod) {
				// ⊢TPL ⊤.
				if _, pms = prfG.AddLine(wffG, pr.TopI); pms == pr.StatusOK {
					tot += 1
				}
			}
		case fmla.Bot: // G is ⊥.
		case fmla.Equal: // G is a=b.
			if pr.RuleFitsStrengths(pr.EqualI, inf, mod) {
				var args []fmla.Argument

				if args = wffG.Args(); args[0] == args[1] { // G is a=a.
					// ⊢TNLi a=a.
					if _, pms = prfG.AddLine(wffG, pr.EqualI); pms == pr.StatusOK {
						tot += 1
					}
				} else {
					newG = fmla.NewAtomicWff(fmla.Equal, args[0], args[0])

					if _, pms = prfG.AddLine(newG, pr.EqualI); pms == pr.StatusOK {
						tot += 1
					}

					newG = fmla.NewAtomicWff(fmla.Equal, args[1], args[1])

					if _, pms = prfG.AddLine(newG, pr.EqualI); pms == pr.StatusOK {
						tot += 1
					}
				}
			}
		default:
		}
	case fmla.To: // G is A→B.
		if pr.RuleFitsStrengths(pr.ToI, inf, mod) {
			// [A…B]→I ⊢TPL A→B.
			subL, subR, _ = wffG.Subs()

			if prfI, pms = prfG.AddPrf(subL, subR, wffG, pr.ToI); pms == pr.StatusOK { // ⊢TPL A.
				tot += 1 + goalAssume(prfI, subR, inf, mod)
			}
		}

		if pr.RuleFitsStrengths(pr.BoxCon, inf, mod) {
			if subL, subR, _ = wffG.Subs(); subL.Mop() == fmla.Box && subR.Mop() == fmla.Box { // G is □A→□B.
				// If ⊢ A→B,B→A, then A→B,B→A ⊢PPL+Ew □A→□B.
				newA, newG = fmla.NewAtomicWff(fmla.Top), fmla.NewBinaryWff(fmla.To, subL.SubL(), subR.SubL())

				if prfI, pms = prfG.AddPrf(newA, newG, newG, pr.Thm); pms == pr.StatusOK {
					tot += 1 + goalAssume(prfI, newG, inf, mod)
				}

				newG = fmla.NewBinaryWff(fmla.To, subR.SubL(), subL.SubL())

				if prfI, pms = prfG.AddPrf(newA, newG, newG, pr.Thm); pms == pr.StatusOK {
					tot += 1 + goalAssume(prfI, newG, inf, mod)
				}
			} else if subL.Mop() == fmla.Dmd && subR.Mop() == fmla.Dmd { // G is ◇A→◇B.
				// If ⊢ A→B,B→A, then A→B,B→A ⊢PPL+Ew ◇A→◇B.
				newA, newG = fmla.NewAtomicWff(fmla.Top), fmla.NewBinaryWff(fmla.To, subL.SubL(), subR.SubL())

				if prfI, pms = prfG.AddPrf(newA, newG, newG, pr.Thm); pms == pr.StatusOK {
					tot += 1 + goalAssume(prfI, newG, inf, mod)
				}

				newG = fmla.NewBinaryWff(fmla.To, subR.SubL(), subL.SubL())

				if prfI, pms = prfG.AddPrf(newA, newG, newG, pr.Thm); pms == pr.StatusOK {
					tot += 1 + goalAssume(prfI, newG, inf, mod)
				}
			}
		}

		if pr.RuleFitsStrengths(pr.BoxMon, inf, mod) {
			if subL, subR, _ = wffG.Subs(); subL.Mop() == fmla.Box && subR.Mop() == fmla.Box { // G is □A→□B.
				// If ⊢ A→B, then A→B ⊢PPL+M □A→□B.
				newA, newG = fmla.NewAtomicWff(fmla.Top), fmla.NewBinaryWff(fmla.To, subL.SubL(), subR.SubL())

				if prfI, pms = prfG.AddPrf(newA, newG, newG, pr.Thm); pms == pr.StatusOK {
					tot += 1 + goalAssume(prfI, newG, inf, mod)
				}
			} else if subL.Mop() == fmla.Dmd && subR.Mop() == fmla.Dmd { // G is ◇A→◇B.
				// If ⊢ A→B, then A→B ⊢PPL+M ◇A→◇B.
				newA, newG = fmla.NewAtomicWff(fmla.Top), fmla.NewBinaryWff(fmla.To, subL.SubL(), subR.SubL())

				if prfI, pms = prfG.AddPrf(newA, newG, newG, pr.Thm); pms == pr.StatusOK {
					tot += 1 + goalAssume(prfI, newG, inf, mod)
				}
			}
		}
	case fmla.Wedge: // G is A∧B.
		if pr.RuleFitsStrengths(pr.WedgeI, inf, mod) {
			// A,B ⊢PPL A∧B.
			subL, subR, _ = wffG.Subs()

			tot += goalAssume(prfG, subL, inf, mod) + goalAssume(prfG, subR, inf, mod)
		}
	case fmla.Vee: // G is A∨B.
		if pr.RuleFitsStrengths(pr.VeeI, inf, mod) {
			// A ⊢PPL A∨B; A ⊢PPL B∨A.
			subL, subR, _ = wffG.Subs()

			tot += goalAssume(prfG, subL, inf, mod) + goalAssume(prfG, subR, inf, mod)
		}

		if pr.RuleFitsStrengths(pr.Jan, inf, mod) {
			if subL, subR, _ = wffG.Subs(); subL.Mop() == fmla.Neg && subR.Mop() == fmla.Neg { // G is ¬A∨¬B.
				// A→¬B ⊢JPL ¬A∨¬B.
				newG = fmla.NewBinaryWff(fmla.To, subL.SubL(), subR)

				tot += goalAssume(prfG, newG, inf, mod)
			}
		}

		if pr.RuleFitsStrengths(pr.Göd, inf, mod) {
			subL, subR, _ = wffG.Subs()

			if subL.Mop() == fmla.To { // G is (B→A)∨C.
				// (A→B)→C ⊢GPL (B→A)∨C.
				newG = fmla.MustParseWffFromTemplate("(%s→%s)→%s", subL.SubR(), subL.SubL(), subR)

				tot += goalAssume(prfG, newG, inf, mod)
			}

			if subR.Mop() == fmla.To { // G is C∨(B→A).
				// (A→B)→C ⊢GPL C∨(B→A).
				newG = fmla.MustParseWffFromTemplate("(%s→%s)→%s", subR.SubR(), subR.SubL(), subL)

				tot += goalAssume(prfG, newG, inf, mod)
			}
		}

		if pr.RuleFitsStrengths(pr.Sme, inf, mod) {
			subL, subR, _ = wffG.Subs()

			if subL.Mop() == fmla.Neg { // G is ¬B∨A.
				// (A→B)→A ⊢SPL ¬B∨A.
				newG = fmla.MustParseWffFromTemplate("(%s→%s)→%s", subR, subL.SubL(), subR)

				tot += goalAssume(prfG, newG, inf, mod)
			}

			if subR.Mop() == fmla.Neg { // G is A∨¬B.
				// (A→B)→A ⊢SPL A∨¬B.
				newG = fmla.MustParseWffFromTemplate("(%s→%s)→%s", subL, subR.SubL(), subL)

				tot += goalAssume(prfG, newG, inf, mod)
			}
		}
	case fmla.Iff: // G is A↔B.
		if pr.RuleFitsStrengths(pr.IffI, inf, mod) {
			// A→B,B→A ⊢PPL A↔B.
			subL, subR, _ = wffG.Subs()

			subL, subR = fmla.NewBinaryWff(fmla.To, subL, subR), fmla.NewBinaryWff(fmla.To, subR, subL)

			tot += goalAssume(prfG, subL, inf, mod) + goalAssume(prfG, subR, inf, mod)
		}
	case fmla.Neg: // G is ¬A.
		if pr.RuleFitsStrengths(pr.NegI, inf, mod) {
			// [A…⊥]¬I ⊢MPL ¬A.
			subL, subR = wffG.SubL(), fmla.NewAtomicWff(fmla.Bot)

			if prfI, pms = prfG.AddPrf(subL, subR, wffG, pr.NegI); pms == pr.StatusOK {
				tot += 1 + goalAssume(prfI, subR, inf, mod)
			}
		}

		if pr.RuleFitsStrengths(pr.BoxIntEw, inf, mod) {
			switch wffG.String() {
			case "¬◇⊥": // G is ¬◇⊥.
				// □⊤ ⊢MPL+Ew ¬◇⊥.
				newG = fmla.MustParseWff("□⊤")

				tot += goalAssume(prfG, newG, inf, mod)
			case "¬◇⊤": // G is ¬◇⊤.
				// □⊥ ⊢MPL+Ew ¬◇⊤.
				newG = fmla.MustParseWff("□⊥")

				tot += goalAssume(prfG, newG, inf, mod)
			}
		}

		if pr.RuleFitsStrengths(pr.DmdIntEw, inf, mod) {
			switch wffG.String() {
			case "¬□⊥": // G is ¬□⊥.
				// ◇⊤ ⊢MPL+Ew ¬□⊥.
				newG = fmla.MustParseWff("◇⊤")

				tot += goalAssume(prfG, newG, inf, mod)
			case "¬□⊤": // G is ¬□⊤.
				// ◇⊥ ⊢MPL+Ew ¬□⊤.
				newG = fmla.MustParseWff("◇⊥")

				tot += goalAssume(prfG, newG, inf, mod)
			}
		}

		if pr.RuleFitsStrengths(pr.BoxIntEn, inf, mod) {
			if wffG.SubL().Mop() == fmla.Dmd { // G is ¬◇A.
				if wffG.Locate("LL").Mop() == fmla.Neg { // G is ¬◇¬A.
					// □A ⊢MPL+En ¬◇¬A.
					newG = fmla.NewUnaryWff(fmla.Box, wffG.Locate("LLL"))
				} else {
					// □¬A ⊢MPL+En ¬◇A.
					newG = fmla.MustParseWffFromTemplate("□¬%s", wffG.Locate("LL"))
				}

				tot += goalAssume(prfG, newG, inf, mod)
			}
		}

		if pr.RuleFitsStrengths(pr.DmdIntEn, inf, mod) {
			if wffG.SubL().Mop() == fmla.Box { // G is ¬□A.
				if wffG.Locate("LL").Mop() == fmla.Neg { // G is ¬□¬A.
					// ◇A ⊢MPL+En ¬□¬A.
					newG = fmla.NewUnaryWff(fmla.Dmd, wffG.Locate("LLL"))
				} else {
					// ◇¬A ⊢MPL+En ¬□A.
					newG = fmla.MustParseWffFromTemplate("◇¬%s", wffG.Locate("LL"))
				}

				tot += goalAssume(prfG, newG, inf, mod)
			}
		}

		if pr.RuleFitsStrengths(pr.NegDmdI, inf, mod) {
			if wffG.SubL().Mop() == fmla.Dmd { // G is ¬◇A.
				// [⊤…¬A]¬◇I ⊢MPL+N ¬◇A.
				subL, subR = fmla.NewAtomicWff(fmla.Top), fmla.NewUnaryWff(fmla.Neg, wffG.Locate("LL"))

				if prfI, pms = prfG.AddPrf(subL, subR, wffG, pr.NegDmdI); pms == pr.StatusOK {
					tot += 1 + goalAssume(prfI, subR, inf, mod)
				}
			}
		}
	case fmla.ForAll: // G is ∀xΦ(x) or ∀XΦ(X).
		if pr.RuleFitsStrengths(pr.ForAllI, inf, mod) {
			var (
				pv, pc fmla.Predicate
				av, ac fmla.Argument
			)

			if pv, av, _ = wffG.Var(); pv != fmla.NoPred { // G is ∀XΦ(X).
				// [⊤…Φ(A)]∀I ⊢P2QL ∀XΦ(X/A)
				pc = prfG.FreshPC()

				newG = wffG.Instantiate(pc)
			} else if av != fmla.NoArg { // G is ∀xΦ(x).
				// [⊤…Φ(a)]∀I ⊢P1QL ∀xΦ(x/a).
				ac = prfG.FreshAC()

				newG = wffG.Instantiate(ac)
			}

			if newG != nil {
				subL = fmla.NewAtomicWff(fmla.Top)

				if prfI, pms = prfG.AddPrf(subL, newG, wffG, pr.ForAllI); pms == pr.StatusOK {
					tot += 1 + goalAssume(prfI, newG, inf, mod)
				}
			}
		}
	case fmla.Exists: // G is ∃XΦ(X) or ∃xΦ(x).
		if pr.RuleFitsStrengths(pr.ExistsI, inf, mod) {
			var (
				pv, pc fmla.Predicate
				av, ac fmla.Argument
			)

			if pv, av, _ = wffG.Var(); pv != fmla.NoPred { // G is ∃XΦ(X) or ∃XΦ(~X~).
				// Φ(A) ⊢P2QL ∃XΦ(X/A).
				if wffG.IsVacuous() { // G is ∃XΦ(~X~).
					tot += goalAssume(prfG, wffG.SubL(), inf, mod)
				} else { // G is ∃XΦ(X).
					for _, pc = range prfG.UsedPCs() {
						newG = wffG.Instantiate(pc)

						tot += goalAssume(prfG, newG, inf, mod)
					}
				}
			} else if av != fmla.NoArg { // G is ∃xΦ(x) or ∃xΦ(~x~).
				// A(a) ⊢P1QL ∃xΦ(x/a).
				if wffG.IsVacuous() { // G is ∃xΦ(~x~).
					tot += goalAssume(prfG, wffG.SubL(), inf, mod)
				} else { // G is ∃xΦ(x).
					for _, ac = range prfG.UsedACs() {
						newG = wffG.Instantiate(ac)

						tot += goalAssume(prfG, newG, inf, mod)
					}
				}
			}
		}
	case fmla.Box: // G is □A.
		if pr.RuleFitsStrengths(pr.BoxI, inf, mod) {
			// [⊤…A]□I ⊢PPL+N □A.
			subL = fmla.NewAtomicWff(fmla.Top)

			if prfI, pms = prfG.AddPrf(subL, wffG.SubL(), wffG, pr.BoxI); pms == pr.StatusOK {
				tot += 1 + goalAssume(prfI, wffG.SubL(), inf, mod)
			}
		}

		if pr.RuleFitsStrengths(pr.BoxAgg, inf, mod) {
			if wffG.SubL().Mop() == fmla.Wedge { // G is □(A∧B).
				// □A,□B ⊢PPL+C □(A∧B).
				newG = fmla.MustParseWffFromTemplate("□%s∧□%s", wffG.Locate("LL"), wffG.Locate("LR"))

				tot += goalAssume(prfG, newG, inf, mod)
			}
		}

		if pr.RuleFitsStrengths(pr.Intro4, inf, mod) {
			if wffG.SubL().Mop() == fmla.Box { // G is □□A.
				// □A ⊢PPL+4 □□A.
				tot += goalAssume(prfG, wffG.SubL(), inf, mod)
			}
		}

		if pr.RuleFitsStrengths(pr.IntroB, inf, mod) {
			if wffG.SubL().Mop() == fmla.Dmd { // G is □◇A.
				tot += goalAssume(prfG, wffG.Locate("LL"), inf, mod)
			}
		}

		if pr.RuleFitsStrengths(pr.Intro5, inf, mod) {
			if wffG.SubL().Mop() == fmla.Dmd { // G is □◇A.
				// ◇A ⊢PPL+5 □◇A.
				tot += goalAssume(prfG, wffG.SubL(), inf, mod)
			}
		}
	case fmla.Dmd: // G is ◇A.
		if pr.RuleFitsStrengths(pr.DmdI, inf, mod) {
			// ¬□¬A ⊢CPL+Ew ◇A.
			newG = fmla.MustParseWffFromTemplate("¬□¬%s", wffG.SubL())

			tot += goalAssume(prfG, newG, inf, mod)
		}

		if pr.RuleFitsStrengths(pr.RuleD, inf, mod) {
			// □A ⊢PPL+D ◇A.
			newG = fmla.NewUnaryWff(fmla.Box, wffG.SubL())

			tot += goalAssume(prfG, newG, inf, mod)
		}

		if pr.RuleFitsStrengths(pr.IntroT, inf, mod) {
			// A ⊢PPL+T ◇A.
			tot += goalAssume(prfG, wffG.SubL(), inf, mod)
		}
	default:
		panic("Unrecognized main operator.")
	}

	return
}
