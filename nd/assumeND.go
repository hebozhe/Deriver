package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
)

func goalAssume(prfG *pr.Prf, wffG *fmla.Wff, inf pr.InfSt, mod pr.ModSt) (tot int) {
	var (
		bot, top, subL, subR, newA, newG *fmla.Wff
		prfO, prfI                       *pr.Prf
		pms                              pr.PrfMutStatus
		lnA                              *pr.Line
	)

	if prfG.HasWff(wffG) {
		goto GOALASSUME_END
	}

	bot, top = fmla.NewAtomicWff(fmla.Bot), fmla.NewAtomicWff(fmla.Top)

	switch wffG.Mop() {
	case fmla.NoSym:
		switch wffG.Pred() {
		case fmla.Top: // G is ⊤.
			if pr.RuleFitsStrengths(pr.TopI, inf, mod) {
				// ⊢TPL ⊤.
				if _, pms = prfG.AddLine(top, pr.TopI); pms == pr.StatusOK {
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
		default: // G is A.
			if pr.RuleFitsStrengths(pr.NegE, inf, mod) {
				// ¬¬A ⊢CPL A.
				newG = fmla.NewUnaryWff(fmla.Neg, fmla.NewUnaryWff(fmla.Neg, wffG))

				tot += goalAssume(prfG, newG, inf, mod)
			}
		}
	case fmla.To: // G is A→B.
		if pr.RuleFitsStrengths(pr.ToI, inf, mod) {
			// [A…B]→I ⊢TPL A→B.
			subL, subR, _ = wffG.Subs() // WARNING! Do not reassign subL or subR beyond this point.

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
			subL, subR, _ = wffG.Subs() // WARNING! Do not reassign subL or subR beyond this point.

			tot += goalAssume(prfG, subL, inf, mod) + goalAssume(prfG, subR, inf, mod)
		}

		if pr.RuleFitsStrengths(pr.Jan, inf, mod) && (wffG.Has(fmla.Neg) || wffG.Has(bot)) {
			// ¬A→B,¬¬A→C ⊢JPL B∨C; ¬¬A→B,¬A→C ⊢JPL B∨C.
			for _, newA = range wffG.AllSubs(true, true) {
				if newA.Mop() == fmla.Neg && newA.SubL().Mop() != fmla.Neg {
					for range 2 {
						newG = fmla.NewBinaryWff(fmla.To, newA, subL)

						tot += goalAssume(prfG, newG, inf, mod)

						newG = fmla.NewBinaryWff(fmla.To, newA, subR)

						tot += goalAssume(prfG, newG, inf, mod)

						newA = fmla.NewUnaryWff(fmla.Neg, newA)
					}
				} else if newA.Mop() != fmla.Neg && !newA.Is(bot) && newA.Has(fmla.Bot) {
					for range 2 {
						newA = fmla.NewUnaryWff(fmla.Neg, newA)

						newG = fmla.NewBinaryWff(fmla.To, newA, subL)

						tot += goalAssume(prfG, newG, inf, mod)

						newG = fmla.NewBinaryWff(fmla.To, newA, subR)

						tot += goalAssume(prfG, newG, inf, mod)
					}
				}
			}
		}

		if pr.RuleFitsStrengths(pr.Göd, inf, mod) {
			// (A→B)→C,(B→A)→D ⊢GPL C∨D. (A→B)→B,(B→A)→A ⊣⊢GPL A∨B.
			newA = fmla.NewBinaryWff(fmla.To, subL, subR)

			newG = fmla.NewBinaryWff(fmla.To, newA, subR)

			tot += goalAssume(prfG, newG, inf, mod)

			newA = fmla.NewBinaryWff(fmla.To, subR, subL)

			newG = fmla.NewBinaryWff(fmla.To, newA, subL)

			tot += goalAssume(prfG, newG, inf, mod)
		}

		if pr.RuleFitsStrengths(pr.Sme, inf, mod) {
			// ¬A→B,(B→A)→C ⊢SPL B∨C. ¬A→B,(B→A)→A ⊣⊢SPL A∨B.
			newG = fmla.NewBinaryWff(fmla.To, fmla.NewUnaryWff(fmla.Neg, subL), subR)

			tot += goalAssume(prfG, newG, inf, mod)

			newG = fmla.NewBinaryWff(fmla.To, fmla.NewUnaryWff(fmla.Neg, subR), subL)

			tot += goalAssume(prfG, newG, inf, mod)
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
			if prfI, pms = prfG.AddPrf(wffG.SubL(), bot, wffG, pr.NegI); pms == pr.StatusOK {
				tot += 1
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
					newG = fmla.MustParseWffFmt("□¬%s", wffG.Locate("LL"))
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
					newG = fmla.MustParseWffFmt("◇¬%s", wffG.Locate("LL"))
				}

				tot += goalAssume(prfG, newG, inf, mod)
			}
		}

		if pr.RuleFitsStrengths(pr.BoxIntEs, inf, mod) {
			if wffG.SubL().Mop() == fmla.Dmd { // G is ¬◇A.
				// If ⊢ A→¬B, □A,A→¬B ⊢MPL+Es ¬◇B.
				newA, subR = fmla.NewAtomicWff(fmla.Top), fmla.NewUnaryWff(fmla.Neg, wffG.Locate("LL"))

				for prfO = range prfG.Root(prfG.DepthM()).WalkPrfPairs(pr.DistPIs(0)) {
					for _, lnA = range keepLines(nil, prfO, mopIs(fmla.Box)) {
						newG = fmla.NewBinaryWff(fmla.To, lnA.Wff().SubL(), subR)

						if prfI, pms = prfG.AddPrf(newA, newG, newG, pr.Thm); pms == pr.StatusOK {
							tot += 1 + goalAssume(prfI, newG, inf, mod)
						}
					}
				}
			}
		}

		if pr.RuleFitsStrengths(pr.DmdIntEs, inf, mod) {
			if wffG.SubL().Mop() == fmla.Box { // G is ¬□A.
				// If ⊢ A→¬B, ◇A,A→¬B ⊢MPL+Es ¬□B.
				newA, subR = fmla.NewAtomicWff(fmla.Top), fmla.NewUnaryWff(fmla.Neg, wffG.Locate("LL"))

				for prfO = range prfG.Root(prfG.DepthM()).WalkPrfPairs(pr.DistPIs(0)) {
					for _, lnA = range keepLines(nil, prfO, mopIs(fmla.Dmd)) {
						newG = fmla.NewBinaryWff(fmla.To, lnA.Wff().SubL(), subR)

						if prfI, pms = prfG.AddPrf(newA, newG, newG, pr.Thm); pms == pr.StatusOK {
							tot += 1 + goalAssume(prfI, newG, inf, mod)
						}
					}
				}
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

		if pr.RuleFitsStrengths(pr.NegE, inf, mod) {
			// ¬¬∃XΦ(X) ⊢CPL ∃XΦ(X); ¬¬∃XΦ(x) ⊢CPL ∃XΦ(x).
			newG = fmla.NewUnaryWff(fmla.Neg, fmla.NewUnaryWff(fmla.Neg, wffG))

			tot += goalAssume(prfG, newG, inf, mod)
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
				newG = fmla.MustParseWffFmt("□%s∧□%s", wffG.Locate("LL"), wffG.Locate("LR"))

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
			newG = fmla.MustParseWffFmt("¬□¬%s", wffG.SubL())

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

GOALASSUME_END:
	return
}

func lineAssume(prfG *pr.Prf, inf pr.InfSt, mod pr.ModSt) (tot int) {
	var (
		ln                                      *pr.Line
		wff, wffG, subL, subR, newA, addW, newG *fmla.Wff
		prfI                                    *pr.Prf
		pms                                     pr.PrfMutStatus
	)

	for ln = range prfG.Lines() {
		switch wff, wffG = ln.Wff(), prfG.WffG(); wff.Mop() {
		case fmla.To: // W is A→B.
			subL, subR, _ = wff.Subs()

			if pr.RuleFitsStrengths(pr.ToE, inf, mod) {
				for prfI = range prfG.Leaves(prfG.DepthM(), true) {
					if !prfI.HasWff(subR) {
						tot += goalAssume(prfI, subL, inf, mod)
					}
				}
			}

			if pr.RuleFitsStrengths(pr.Jan, inf, mod) {
				if subL.Mop() == fmla.Neg { // W is ¬A→B.
					if subL.SubL().Mop() == fmla.Neg { // W is ¬¬A→B.
						newA = subL.SubL()
					} else {
						newA = fmla.NewUnaryWff(fmla.Neg, subL)
					}

					newG = fmla.NewBinaryWff(fmla.To, newA, wffG) // Prove ¬A→G or ¬¬A→G.

					tot += goalAssume(prfG, newG, inf, mod)
				}
			}

			if pr.RuleFitsStrengths(pr.Göd, inf, mod) {
				if subL.Mop() == fmla.To {
					newG = fmla.NewBinaryWff(fmla.To, subL, subL.SubR()) // Prove (A→B)→B.

					tot += goalAssume(prfG, newG, inf, mod)

					newA = fmla.NewBinaryWff(fmla.To, subL.SubR(), subL.SubL())

					newG = fmla.NewBinaryWff(fmla.To, newA, subL.SubL()) // Prove (B→A)→A.

					tot += goalAssume(prfG, newG, inf, mod)
				}
			}

			if pr.RuleFitsStrengths(pr.Sme, inf, mod) {
				if subL.Mop() == fmla.Neg { // W is ¬A→B.
					newA = fmla.NewBinaryWff(fmla.To, subR, subL.SubL()) // Prove (B→A)→A.

					newG = fmla.NewBinaryWff(fmla.To, newA, subL.SubL())

					tot += goalAssume(prfG, newG, inf, mod)
				} else if subL.Mop() == fmla.To && subL.SubR().Is(subR) { // W is (A→B)→B.
					newA = fmla.NewUnaryWff(fmla.Neg, subR)

					newG = fmla.NewBinaryWff(fmla.To, newA, subL.SubL()) // Prove ¬B→A.

					tot += goalAssume(prfG, newG, inf, mod)
				}
			}
		case fmla.Wedge: // W is A∧B.
			if pr.RuleFitsStrengths(pr.WedgeE, inf, mod) {
				if _, pms = prfG.AddLine(wff.SubL(), pr.WedgeE, ln); pms == pr.StatusOK { // Derive A.
					tot += 1
				}

				if _, pms = prfG.AddLine(wff.SubR(), pr.WedgeE, ln); pms == pr.StatusOK { // Derive B.
					tot += 1
				}
			}
		case fmla.Vee: // W is A∨B.
			subL, subR, _ = wff.Subs()

			if pr.RuleFitsStrengths(pr.VeeE, inf, mod) {
				if wff.SubL().Is(wff.SubR()) { // W is A∨A.
					newG = fmla.NewBinaryWff(fmla.To, subL, subL) // Prove A→A.

					tot += goalAssume(prfG, newG, inf, mod)
				} else {
					newG = fmla.NewBinaryWff(fmla.To, subL, wffG) // Prove A→G.

					tot += goalAssume(prfG, newG, inf, mod)

					newG = fmla.NewBinaryWff(fmla.To, subR, wffG) // Prove B→G.

					tot += goalAssume(prfG, newG, inf, mod)
				}
			}
		case fmla.Iff: // W is A↔B.
			if pr.RuleFitsStrengths(pr.IffE, inf, mod) {
				addW = fmla.NewBinaryWff(fmla.To, wff.SubL(), wff.SubR())

				if _, pms = prfG.AddLine(addW, pr.IffE, ln); pms == pr.StatusOK { // Derive A→B.
					tot += 1
				}

				addW = fmla.NewBinaryWff(fmla.To, addW.SubR(), addW.SubL())

				if _, pms = prfG.AddLine(addW, pr.IffE, ln); pms == pr.StatusOK { // Derive B→A.
					tot += 1
				}
			}
		case fmla.Neg: // W is ¬A.
			subL = wff.SubL()

			if pr.RuleFitsStrengths(pr.NegE, inf, mod) && subL.Mop() == fmla.Neg { // W is ¬¬A.
				if _, pms = prfG.AddLine(subL.SubL(), pr.NegE, ln); pms == pr.StatusOK { // Derive A.
					tot += 1
				}
			}

			if pr.RuleFitsStrengths(pr.BotI, inf, mod) {
				for prfI = range prfG.Leaves(prfG.DepthM(), true) {
					if !prfI.HasWff(subL) {
						tot += goalAssume(prfI, subL, inf, mod)
					}
				}
			}
		case fmla.Exists: // W is ∃XΦ(X) or ∃xΦ(x).
			if pr.RuleFitsStrengths(pr.ExistsE, inf, mod) {
				var (
					pv, pc fmla.Predicate
					av, ac fmla.Argument
				)

				if pv, av, _ = wff.Var(); pv != fmla.NoPred { // W is ∃XΦ(X).
					pc = prfG.FreshPC()

					newA = wff.Instantiate(pc) // Φ(A/X).
				} else if av != fmla.NoArg { // W is ∃xΦ(x).
					ac = prfG.FreshAC()

					newA = wff.Instantiate(ac) // Φ(a/x).
				}

				if prfI, pms = prfG.AddPrf(newA, wffG, wffG, pr.ExistsE, ln); pms == pr.StatusOK {
					tot += 1 + goalAssume(prfI, wffG, inf, mod)
				}
			}
		case fmla.Box: // W is □A.
			var (
				prfT *pr.Prf
				trg  *fmla.Wff
			)

			for prfT, trg = range prfG.Root(prfG.DepthM()).WalkTargets(pr.SeesAll(prfG)) {
				if trg.Mop() != fmla.Box || prfT.DistM(prfG)*prfG.DistM(prfT) != 0 {
					continue
				}

				if prfI, pms = ln.Prf().AddPrf(wff.SubL(), trg.SubL(), trg, pr.BoxE, ln); pms == pr.StatusOK {
					tot += 1 + goalAssume(prfI, trg.SubL(), inf, mod)
				}
			}
		case fmla.Dmd: // W is ◇A.
			var (
				prfT *pr.Prf
				trg  *fmla.Wff
			)

			for prfT, trg = range prfG.Root(prfG.DepthM()).WalkTargets(pr.SeesAll(prfG)) {
				if trg.Mop() != fmla.Dmd || prfT.DistM(prfG)*prfG.DistM(prfT) != 0 {
					continue
				}

				if prfI, pms = prfG.AddPrf(wff.SubL(), trg.SubL(), trg, pr.DmdE, ln); pms == pr.StatusOK {
					tot += 1 + goalAssume(prfI, trg.SubL(), inf, mod)
				}
			}
		}
	}

	if prfG.IsOpen() {
		for prfI = range prfG.PrfsI() {
			if prfI.IsOpen() {
				tot += lineAssume(prfI, inf, mod)
			}
		}
	}

	return
}
