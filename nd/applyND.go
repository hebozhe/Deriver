package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
	"slices"
)

type ndRuleFunc func(prf *pr.Prf) (tot int)

var ndTopI ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfT *pr.Prf
		trg  *fmla.Wff
		pms  pr.PrfMutStatus
	)

	// ⊢TPL ⊤.
	for prfT, trg = range prf.WalkTargets() {
		if trg.Pred() != fmla.Top {
			continue
		}

		if _, pms = prfT.AddLine(trg, pr.TopI); pms == pr.StatusOK { // ⊢TPL ⊤.
			tot += 1
		}
	}

	return
}

var ndToI ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		j1, j2     *pr.Line
		pms        pr.PrfMutStatus
	)

	// [A…B]→I ⊢TPL A→B.
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistPIs(1), pr.PurpIs(pr.ToI)) {
		if j1 = prfI.LineAtIndex(0); j1 == nil || j1.Rule() != pr.Ass { // [A…]→I.
			continue
		}

		if j2 = prfI.LineWithWff(prfI.WffG()); j2 == nil { // […B]→I.
			continue
		}

		if _, pms = prfO.AddLine(prfI.WffD(), pr.ToI, j1, j2); pms == pr.StatusOK { // ⊢TPL A→B.
			tot, _, _ = tot+1, prfI.Close(), prfI.Prune()
		}
	}

	return
}

var ndToE ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		js1, js2   []*pr.Line
		j1, j2     *pr.Line
		pms        pr.PrfMutStatus
	)

	// A→B,A ⊢TPL B.
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistMIs(0)) {
		js1 = keepLines(prfO, prfI, mopIs(fmla.To))

		for _, j1 = range js1 {
			js2 = keepLines(prfO, prfI, wffIs(j1.Wff().SubL())) // A.

			for _, j2 = range js2 {
				if _, pms = prfI.AddLine(j1.Wff().SubR(), pr.ToE, j1, j2); pms == pr.StatusOK { // ⊢TPL B.
					tot += 1
				}
			}
		}
	}

	return
}

var ndReit ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		j1         *pr.Line
		pms        pr.PrfMutStatus
	)

	// A,[…](→I|¬I|∀I|∃E) ⊢TPL […A](→I|¬I|∀I|∃E).
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistMIs(0), pr.PurpIs(pr.ToI, pr.NegI, pr.ForAllI, pr.ExistsE)) { // […](→I|¬I|∀I|∃E)
		if j1 = prfO.LineWithWff(prfI.WffG()); j1 == nil { // A.
			continue
		}

		if _, pms = prfI.AddLine(j1.Wff(), pr.Reit, j1); pms == pr.StatusOK { // ⊢TPL […A](→I|¬I|∀I|∃E).
			tot += 1
		}
	}

	return
}

var ndThm ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		j1, j2     *pr.Line
		pms        pr.PrfMutStatus
	)

	// [⊤…A]Thm ⊢TPL A.
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistPIs(1), pr.PurpIs(pr.Thm)) {
		if j1 = prfI.LineAtIndex(0); j1 == nil || j1.Rule() != pr.Ass { // [⊤…]Thm
			continue
		}

		if j2 = prfI.LineWithWff(prfI.WffG()); j2 == nil { // […A]Thm
			continue
		}

		if _, pms = prfO.AddLine(prfI.WffD(), pr.Thm, j1, j2); pms == pr.StatusOK { // ⊢TPL A.
			tot, _, _ = tot+1, prfI.Close(), prfI.Prune()
		}
	}

	return
}

var ndWedgeI ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI, prfT *pr.Prf
		trg              *fmla.Wff
		js1, js2         []*pr.Line
		j1, j2           *pr.Line
		pms              pr.PrfMutStatus
	)

	// A,B ⊢PPL A∧B.
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistMIs(0)) {
		for prfT, trg = range prf.WalkTargets(pr.SeesAll(prfO, prfI)) {
			if trg.Mop() != fmla.Wedge || prfT.DistM(prfI)*prfI.DistM(prfT) != 0 {
				continue
			}

			js1 = keepLines(prfO, prfI, wffIs(trg.SubL())) // A.

			js2 = keepLines(prfO, prfI, wffIs(trg.SubR())) // B.

			for _, j1 = range js1 {
				for _, j2 = range js2 {
					if _, pms = prfI.AddLine(trg, pr.WedgeI, j1, j2); pms == pr.StatusOK { // ⊢PPL A∧B.
						tot += 1
					}
				}
			}
		}
	}

	return
}

var ndWedgeE ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI *pr.Prf
		js1  []*pr.Line
		j1   *pr.Line
		pms  pr.PrfMutStatus
	)

	// A∧B ⊢PPL A,B.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		js1 = keepLines(nil, prfI, mopIs(fmla.Wedge)) // A∧B.

		for _, j1 = range js1 {
			if _, pms = prfI.AddLine(j1.Wff().SubL(), pr.WedgeE, j1); pms == pr.StatusOK { // ⊢PPL A.
				tot += 1
			}

			if _, pms = prfI.AddLine(j1.Wff().SubR(), pr.WedgeE, j1); pms == pr.StatusOK { // ⊢PPL B.
				tot += 1
			}
		}
	}

	return
}

var ndVeeI ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI, prfT *pr.Prf
		trg        *fmla.Wff
		js1        []*pr.Line
		j1         *pr.Line
		pms        pr.PrfMutStatus
	)

	// A ⊢PPL A∨B; B ⊢PPL A∨B.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		for prfT, trg = range prf.WalkTargets(pr.SeesAll(prfI)) {
			if trg.Mop() != fmla.Vee || prfT.DistM(prfI)*prfI.DistM(prfT) != 0 {
				continue
			}

			js1 = keepLines(nil, prfI, or(wffIs(trg.SubL()), wffIs(trg.SubR()))) // A,B.

			for _, j1 = range js1 {
				if _, pms = prfI.AddLine(trg, pr.VeeI, j1); pms == pr.StatusOK { // ⊢PPL A∨B.
					tot += 1
				}
			}
		}
	}

	return
}

var ndVeeE ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI1, prfI2, prfI *pr.Prf
		js1, js2, js3            []*pr.Line
		j1, j2, j3               *pr.Line
		subL, subR               *fmla.Wff
		pms                      pr.PrfMutStatus
	)

	// A∨B,A→C,B→C ⊢PPL C.
	for prfO = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		js1 = keepLines(nil, prfO, mopIs(fmla.Vee)) // A∨B.

		for _, j1 = range js1 {
			subL, subR, _ = j1.Wff().Subs()

			if subL.Is(subR) { // A∨A.
				for prfI1, prfI2 = range prf.WalkPrfPairs(pr.DistMIs(0), pr.SeesAll(prfO)) {
					if prfI1.DistM(prfO)*prfO.DistM(prfI1) != 0 || prfI2.DistM(prfO)*prfO.DistM(prfI2) != 0 {
						continue
					}

					js2 = keepLines(prfI1, prfI2, mopIs(fmla.To), subIs("L", subL)) // A→B.
					js2 = append(js2, keepLines(nil, prfO, mopIs(fmla.To), subIs("L", subL))...)

					for _, j2 = range js2 {
						prfI = pr.InnermostProof(prfO, prfI1, prfI2)

						if _, pms = prfI.AddLine(j2.Wff().SubR(), pr.VeeE, j1, j2, j2); pms == pr.StatusOK { // ⊢PPL B.
							tot += 1
						}
					}

					continue
				}
			}

			for prfI1, prfI2 = range prf.WalkPrfPairs(pr.DistMIs(0), pr.SeesAll(prfO)) {
				if prfI1.DistM(prfO)*prfO.DistM(prfI1) != 0 || prfI2.DistM(prfO)*prfO.DistM(prfI2) != 0 {
					continue
				}

				js2 = keepLines(prfI1, prfI2, mopIs(fmla.To), subIs("L", subL)) // A→C.
				js2 = append(js2, keepLines(nil, prfO, mopIs(fmla.To), subIs("L", subL))...)

				js3 = keepLines(prfO, prfI1, mopIs(fmla.To), subIs("L", subR)) // B→D.
				js3 = append(js3, keepLines(nil, prfO, mopIs(fmla.To), subIs("L", subR))...)

				for _, j2 = range js2 {
					for _, j3 = range js3 {
						if j2.Wff().SubR().Is(j3.Wff().SubR()) { // A→C,B→C.
							prfI = pr.InnermostProof(prfO, prfI1, prfI2)

							if _, pms = prfI.AddLine(j3.Wff().SubR(), pr.VeeE, j1, j2, j3); pms == pr.StatusOK { // ⊢PPL C.
								tot += 1
							}
						}
					}
				}
			}
		}
	}

	return
}

var ndIffI ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI, prfT *pr.Prf
		trg              *fmla.Wff
		js1, js2         []*pr.Line
		j1, j2           *pr.Line
		pms              pr.PrfMutStatus
	)

	// A→B,B→A ⊢PPL A↔B.
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistMIs(0)) {
		for prfT, trg = range prf.WalkTargets(pr.SeesAll(prfO, prfI)) {
			if trg.Mop() != fmla.Iff || prfT.DistM(prfI)*prfI.DistM(prfT) != 0 {
				continue
			}

			js1 = keepLines(prfO, prfI, mopIs(fmla.To), subIs("L", trg.SubL()), subIs("R", trg.SubR())) // A→B.

			js2 = keepLines(prfO, prfI, mopIs(fmla.To), subIs("L", trg.SubR()), subIs("R", trg.SubL())) // B→A.

			for _, j1 = range js1 {
				for _, j2 = range js2 {
					if _, pms = prfI.AddLine(trg, pr.IffI, j1, j2); pms == pr.StatusOK { // ⊢PPL A↔B.
						tot += 1
					}
				}
			}
		}
	}

	return
}

var ndIffE ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI *pr.Prf
		js1  []*pr.Line
		j1   *pr.Line
		addW *fmla.Wff
		pms  pr.PrfMutStatus
	)

	// A↔B ⊢PPL A→B,B→A.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		js1 = keepLines(nil, prfI, mopIs(fmla.Iff)) // A↔B.

		for _, j1 = range js1 {
			addW = fmla.NewBinaryWff(fmla.To, j1.Wff().SubL(), j1.Wff().SubR()) // A→B.

			if _, pms = prfI.AddLine(addW, pr.IffE, j1); pms == pr.StatusOK { // ⊢PPL A→B.
				tot += 1
			}

			addW = fmla.NewBinaryWff(fmla.To, addW.SubR(), addW.SubL()) // B→A.

			if _, pms = prfI.AddLine(addW, pr.IffE, j1); pms == pr.StatusOK { // ⊢PPL B→A.
				tot += 1
			}
		}
	}

	return
}

var ndBotI ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		addW       *fmla.Wff
		prfO, prfI *pr.Prf
		js1, js2   []*pr.Line
		j1, j2     *pr.Line
		pms        pr.PrfMutStatus
	)

	addW = fmla.NewAtomicWff(fmla.Bot)

	// A,¬A ⊢MPL ⊥.
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistMIs(0)) {
		js2 = keepLines(prfO, prfI, mopIs(fmla.Neg)) // ¬A.

		for _, j2 = range js2 {
			js1 = keepLines(prfO, prfI, wffIs(j2.Wff().SubL())) // A.

			for _, j1 = range js1 {
				if _, pms = prfI.AddLine(addW, pr.BotI, j1, j2); pms == pr.StatusOK { // ⊢MPL ⊥.
					tot += 1
				}
			}
		}
	}

	return
}

var ndBotE ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI *pr.Prf
		js1  []*pr.Line
		j1   *pr.Line
		pms  pr.PrfMutStatus
	)

	// ⊥ ⊢IPL G.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		js1 = keepLines(nil, prfI, predIs(fmla.Bot)) // ⊥.

		for _, j1 = range js1 {
			if _, pms = prfI.AddLine(prfI.WffG(), pr.BotE, j1); pms == pr.StatusOK { // ⊢IPL G.
				tot += 1
			}
		}
	}

	return
}

var ndNegI ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		j1, j2     *pr.Line
		pms        pr.PrfMutStatus
	)

	// [A…⊥]¬I ⊢MPL ¬A.
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistPIs(1), pr.PurpIs(pr.NegI)) {
		if j1 = prfI.LineAtIndex(0); j1 == nil || j1.Rule() != pr.Ass { // [A…]¬I.
			continue
		}

		if j2 = prfI.LineWithWff(prfI.WffG()); j2 == nil { // […⊥]¬I.
			continue
		}

		if _, pms = prfO.AddLine(prfI.WffD(), pr.NegI, j1, j2); pms == pr.StatusOK { // ⊢MPL ¬A.
			tot, _, _ = tot+1, prfI.Close(), prfI.Prune()
		}
	}

	return
}

var ndNegE ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI *pr.Prf
		js1  []*pr.Line
		j1   *pr.Line
		addW *fmla.Wff
		pms  pr.PrfMutStatus
	)

	// ¬¬A ⊢CPL A.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		js1 = keepLines(nil, prfI, mopIs(fmla.Neg), subMopIs("L", fmla.Neg)) // ¬¬A.

		for _, j1 = range js1 {
			addW = j1.Wff().Locate("LL") // A.

			if _, pms = prfI.AddLine(addW, pr.NegE, j1); pms == pr.StatusOK { // ⊢CPL A.
				tot += 1
			}
		}
	}

	return
}

var ndEqualI ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfT *pr.Prf
		trg  *fmla.Wff
		args []fmla.Argument
		pms  pr.PrfMutStatus
	)

	// ⊢TNLi a=a.
	for prfT, trg = range prf.WalkTargets() {
		if args = trg.Args(); trg.Pred() != fmla.Equal || args[0] != args[1] {
			continue
		} else if !slices.Contains(fmla.ArgConsts, args[0]) || !slices.Contains(fmla.ArgConsts, args[1]) {
			continue
		}

		if _, pms = prfT.AddLine(trg, pr.EqualI); pms == pr.StatusOK {
			tot += 1
		}
	}

	return
}

var ndEqualE ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		js1, js2   []*pr.Line
		j1, j2     *pr.Line
		args       []fmla.Argument
		addsW      map[fmla.WffHash]*fmla.Wff
		addW       *fmla.Wff
		pms        pr.PrfMutStatus
	)

	// a=b,Φ(a) ⊢TNLi Φ(b/a); a=b,Φ(b) ⊢TNLi Φ(a/b).
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistMIs(0)) {
		js1 = keepLines(prfO, prfI, predIs(fmla.Equal)) // a=b.

		for _, j1 = range js1 {
			if args = j1.Wff().Args(); args[0] == args[1] {
				continue
			} else if !slices.Contains(fmla.ArgConsts, args[0]) || !slices.Contains(fmla.ArgConsts, args[1]) {
				continue
			}

			js2 = keepLines(prfO, prfI, or(wffHas(args[0]), wffHas(args[1]))) // Φ(a) or Φ(b).

			for _, j2 = range js2 {
				if j2.Wff().Has(args[0]) {
					addsW = j2.Wff().Replace(args[0], args[1], fmla.Box, fmla.Dmd) // Φ(b/a).

					for _, addW = range addsW {
						if _, pms = prfI.AddLine(addW, pr.EqualE, j1, j2); pms == pr.StatusOK { // ⊢TNLi Φ(b/a).
							tot += 1
						}
					}
				}

				if j2.Wff().Has(args[1]) {
					addsW = j2.Wff().Replace(args[1], args[0], fmla.Box, fmla.Dmd) // Φ(a/b).

					for _, addW = range addsW {
						if _, pms = prfI.AddLine(addW, pr.EqualE, j1, j2); pms == pr.StatusOK { // ⊢TNLi Φ(a/b).
							tot += 1
						}
					}
				}
			}
		}
	}

	return
}

var ndJan ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		js1, js2   []*pr.Line
		j1, j2     *pr.Line
		addW       *fmla.Wff
		pms        pr.PrfMutStatus
	)

	// ¬A→B,¬¬A→C ⊢JPL B∨C.
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistMIs(0)) {
		js2 = keepLines(prfO, prfI, mopIs(fmla.To), subMopIs("L", fmla.Neg), subMopIs("LL", fmla.Neg)) // ¬¬A→C.

		for _, j2 = range js2 {
			js1 = keepLines(prfO, prfI, mopIs(fmla.To), subIs("L", j2.Wff().Locate("LL"))) // ¬A→B.

			for _, j1 = range js1 {
				addW = fmla.NewBinaryWff(fmla.Vee, j1.Wff().SubR(), j2.Wff().SubR())

				if _, pms = prfI.AddLine(addW, pr.Jan, j1, j2); pms == pr.StatusOK { // ⊢JPL B∨C.
					tot += 1
				}

				addW = fmla.NewBinaryWff(fmla.Vee, j2.Wff().SubR(), j1.Wff().SubR())

				if _, pms = prfI.AddLine(addW, pr.Jan, j1, j2); pms == pr.StatusOK { // ⊢JPL B∨C.
					tot += 1
				}
			}
		}
	}

	return
}

var ndGöd ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		js1, js2   []*pr.Line
		j1, j2     *pr.Line
		wff, addW  *fmla.Wff
		pms        pr.PrfMutStatus
	)

	// (A→B)→C,(B→A)→D ⊢GPL C∨D.
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistMIs(0)) {
		js1 = keepLines(prfO, prfI, mopIs(fmla.To), subMopIs("L", fmla.To)) // (A→B)→C.

		for _, j1 = range js1 {
			wff = fmla.NewBinaryWff(fmla.To, j1.Wff().Locate("LR"), j1.Wff().Locate("LL"))

			js2 = keepLines(prfO, prfI, mopIs(fmla.To), subIs("L", wff)) // (B→A)→D.

			for _, j2 = range js2 {
				addW = fmla.NewBinaryWff(fmla.Vee, j1.Wff().SubR(), j2.Wff().SubR())

				if _, pms = prfI.AddLine(addW, pr.Göd, j1, j2); pms == pr.StatusOK { // ⊢GPL A∨B.
					tot += 1
				}
			}
		}
	}

	return
}

var ndSme ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		js1, js2   []*pr.Line
		j1, j2     *pr.Line
		wff, addW  *fmla.Wff
		pms        pr.PrfMutStatus
	)

	// ¬A→B,(B→A)→C ⊢SPL B∨C.
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistMIs(0)) {
		js1 = keepLines(prfO, prfI, mopIs(fmla.To), subMopIs("L", fmla.Neg)) // ¬A→B.

		for _, j1 = range js1 {
			wff = fmla.NewBinaryWff(fmla.To, j1.Wff().SubR(), j1.Wff().Locate("LL"))

			js2 = keepLines(prfO, prfI, mopIs(fmla.To), subIs("L", wff)) // (B→A)→C.

			for _, j2 = range js2 {
				addW = fmla.NewBinaryWff(fmla.Vee, j1.Wff().SubR(), j2.Wff().SubR())

				if _, pms = prfI.AddLine(addW, pr.Sme, j1, j2); pms == pr.StatusOK { // ⊢SPL A∨B.
					tot += 1
				}
			}
		}
	}

	return
}

var ndForAllI ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		j1, j2     *pr.Line
		pms        pr.PrfMutStatus
	)

	// [⊤…Φ(A)]∀I ⊢P2QL ∀XΦ(X/A); [⊤…Φ(a)]∀I ⊢P1QL ∀xΦ(x/a).
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistPIs(1), pr.PurpIs(pr.ForAllI)) {
		if j1 = prfI.LineAtIndex(0); j1 == nil || j1.Rule() != pr.Ass { // [A…]∀I.
			continue
		}

		if j2 = prfI.LineWithWff(prfI.WffG()); j2 == nil { // […B]→I.
			continue
		}

		if _, pms = prfO.AddLine(prfI.WffD(), pr.ForAllI, j1, j2); pms == pr.StatusOK { // ⊢TPL A→B.
			tot, _, _ = tot+1, prfI.Close(), prfI.Prune()
		}
	}

	return
}

var ndForAllE ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		js1        []*pr.Line
		j1         *pr.Line
		pv, pc     fmla.Predicate
		av, ac     fmla.Argument
		addW       *fmla.Wff
		pms        pr.PrfMutStatus
	)

	// ∀XΦ(X) ⊢P2QL Φ(A/X); ∀xΦ(x) ⊢P1QL Φ(a/x).
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistMIs(0)) {
		js1 = keepLines(prfO, prfI, mopIs(fmla.ForAll)) // ∀XΦ(X) or ∀xΦ(x).

		for _, j1 = range js1 {
			if pv, av, _ = j1.Wff().Var(); pv != fmla.NoPred { // ∀XΦ(X).
				for _, pc = range prfI.UsedPCs() {
					addW = j1.Wff().Instantiate(pc) // Φ(A/X).

					if _, pms = prfI.AddLine(addW, pr.ForAllE, j1); pms == pr.StatusOK { // ⊢PPL Φ(A/X).
						tot += 1
					}
				}

				if pc == fmla.NoPred {
					pc = prfI.FreshPC()

					addW = j1.Wff().Instantiate(pc) // Φ(A/X).

					if _, pms = prfI.AddLine(addW, pr.ForAllE, j1); pms == pr.StatusOK { // ⊢PPL Φ(A/X).
						tot += 1
					}
				}
			} else if av != fmla.NoArg { // ∀xΦ(x).
				for _, ac = range prfI.UsedACs() {
					addW = j1.Wff().Instantiate(ac) // Φ(a/x).

					if _, pms = prfI.AddLine(addW, pr.ForAllE, j1); pms == pr.StatusOK { // ⊢PPL Φ(a/x).
						tot += 1
					}
				}

				if ac == fmla.NoArg {
					ac = prfI.FreshAC()

					addW = j1.Wff().Instantiate(ac) // Φ(a/x).

					if _, pms = prfI.AddLine(addW, pr.ForAllE, j1); pms == pr.StatusOK { // ⊢PPL Φ(a/x).
						tot += 1
					}
				}
			}
		}
	}

	return
}

var ndExistsI ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI, prfT *pr.Prf
		trg        *fmla.Wff
		pv, pc     fmla.Predicate
		av, ac     fmla.Argument
		wffA       *fmla.Wff
		j1         *pr.Line
		pms        pr.PrfMutStatus
	)

	// Φ(A) ⊢P2QL ∃XΦ(X/A); Φ(a) ⊢P1QL ∃xΦ(x/a).
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		for prfT, trg = range prf.WalkTargets(pr.SeesAll(prfI)) {
			if trg.Mop() != fmla.Exists || !trg.IsClosed() || prfT.DistM(prfI)*prfI.DistM(prfT) != 0 {
				continue
			}

			if pv, av, _ = trg.Var(); pv != fmla.NoPred { // ∃XΦ(X).
				if trg.IsVacuous() {
					if j1 = prfI.LineWithWff(trg.SubL()); j1 != nil { // Φ(~A~).
						if _, pms = prfI.AddLine(trg, pr.ExistsI, j1); pms == pr.StatusOK { // ⊢P2QL ∃XΦ(~X~).
							tot += 1
						}
					}
				} else {
					for _, pc = range prfI.UsedPCs() {
						wffA = trg.Instantiate(pc) // Φ(A).

						if j1 = prfI.LineWithWff(wffA); j1 == nil { // Φ(A).
							continue
						}

						if _, pms = prfI.AddLine(trg, pr.ExistsI, j1); pms == pr.StatusOK { // ⊢P2QL ∃XΦ(X/A).
							tot += 1
						}
					}
				}
			} else if av != fmla.NoArg { // ∃xΦ(x).
				if trg.IsVacuous() {
					if j1 = prfI.LineWithWff(trg.SubL()); j1 != nil { // Φ(~a~).
						if _, pms = prfI.AddLine(trg, pr.ExistsI, j1); pms == pr.StatusOK { // ⊢P1QL ∃xΦ(~x~).
							tot += 1
						}
					}
				} else {
					for _, ac = range prfI.UsedACs() {
						wffA = trg.Instantiate(ac) // Φ(a).

						if j1 = prfI.LineWithWff(wffA); j1 == nil { // Φ(a).
							continue
						}

						if _, pms = prfI.AddLine(trg, pr.ExistsI, j1); pms == pr.StatusOK { // ⊢P1QL ∃xΦ(x/a).
							tot += 1
						}
					}
				}
			}
		}
	}

	return
}

var ndExistsE ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		j1, j2, j3 *pr.Line
		pms        pr.PrfMutStatus
	)

	// ∃XΦ(X),[Φ(A/X)…Ψ(~A~)]∃E ⊢P2QL Ψ(~A~); ∃xΦ(x),[Φ(a/x)…Ψ(~a~)]∃E ⊢P1QL Ψ(~a~).
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistPIs(1), pr.PurpIs(pr.ExistsE)) {
		if j2 = prfI.LineAtIndex(0); j2 == nil || j2.Rule() != pr.Ass { // [Φ(A/X)…]∃E or [Φ(a/x)…]∃E.
			continue
		}

		j1, _, _, _ = j2.Justs()

		if j3 = prfI.LineWithWff(prfI.WffG()); j3 == nil { // […Ψ(~A~)]∃E or […Ψ(~a~)]∃E.
			continue
		}

		if _, pms = prfO.AddLine(prfI.WffD(), pr.ExistsE, j1, j2, j3); pms == pr.StatusOK { // ⊢P2QL Ψ(~A~).
			tot, _, _ = tot+1, prfI.Close(), prfI.Prune()
		}
	}

	return
}

var ndBoxCon ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI   *pr.Prf
		reqs1, reqs2 []func(*pr.Line) bool
		js1, js2     []*pr.Line
		j1, j2       *pr.Line
		addW         *fmla.Wff
		pms          pr.PrfMutStatus
	)

	// If ⊢ A→B,B→A, then A→B,B→A ⊢PPL+Ew □A→□B.
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistMIs(0)) {
		reqs1 = []func(*pr.Line) bool{mopIs(fmla.To), ruleIs(pr.Thm)}

		js1 = keepLines(prfO, prfI, reqs1...)

		for _, j1 = range js1 {
			reqs2 = append(reqs1, subIs("L", j1.Wff().SubR()), subIs("R", j1.Wff().SubL()))

			js2 = keepLines(prfO, prfI, reqs2...)

			for _, j2 = range js2 {
				addW = fmla.MustParseWffFmt("□%s→□%s", j1.Wff().SubL(), j1.Wff().SubR())

				if _, pms = prfO.AddLine(addW, pr.BoxCon, j1, j2); pms == pr.StatusOK { // ⊢PPL+Ew □A→□B.
					tot += 1
				}
			}
		}
	}

	return
}

var ndDmdCon ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI   *pr.Prf
		reqs1, reqs2 []func(*pr.Line) bool
		js1, js2     []*pr.Line
		j1, j2       *pr.Line
		addW         *fmla.Wff
		pms          pr.PrfMutStatus
	)

	// If ⊢ A→B,B→A, then A→B,B→A ⊢PPL+Ew ◇A→◇B.
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistMIs(0)) {
		reqs1 = []func(*pr.Line) bool{mopIs(fmla.To), ruleIs(pr.Thm)}

		js1 = keepLines(prfO, prfI, reqs1...)

		for _, j1 = range js1 {
			reqs2 = append(reqs1, subIs("L", j1.Wff().SubR()), subIs("R", j1.Wff().SubL()))

			js2 = keepLines(prfO, prfI, reqs2...)

			for _, j2 = range js2 {
				addW = fmla.MustParseWffFmt("◇%s→◇%s", j1.Wff().SubL(), j1.Wff().SubR())

				if _, pms = prfO.AddLine(addW, pr.DmdCon, j1, j2); pms == pr.StatusOK { // ⊢PPL+Ew ◇A→◇B.
					tot += 1
				}
			}
		}
	}

	return
}

var ndBoxIntEw ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI *pr.Prf
		js1  []*pr.Line
		j1   *pr.Line
		addW *fmla.Wff
		pms  pr.PrfMutStatus
	)

	// □⊤ ⊢MPL+Ew ¬◇⊥; □⊥ ⊢MPL+Ew ¬◇⊤.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		js1 = keepLines(nil, prfI, strIs("□⊤")) // □⊤.

		addW = fmla.MustParseWff("¬◇⊥") // ¬◇⊥.

		for _, j1 = range js1 {
			if _, pms = prfI.AddLine(addW, pr.BoxIntEw, j1); pms == pr.StatusOK { // ⊢MPL+Ew ¬◇⊥.
				tot += 1
			}
		}

		js1 = keepLines(nil, prfI, strIs("□⊥")) // □⊥.

		addW = fmla.MustParseWff("¬◇⊤") // ¬◇⊤.

		for _, j1 = range js1 {
			if _, pms = prfI.AddLine(addW, pr.BoxIntEw, j1); pms == pr.StatusOK { // ⊢MPL+Ew ¬◇⊤.
				tot += 1
			}
		}
	}

	return
}

var ndDmdIntEw ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI *pr.Prf
		js1  []*pr.Line
		j1   *pr.Line
		addW *fmla.Wff
		pms  pr.PrfMutStatus
	)

	// ◇⊤ ⊢MPL+Ew ¬□⊥; ◇⊥ ⊢MPL+Ew ¬□⊤.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		js1 = keepLines(nil, prfI, strIs("◇⊤")) // ◇⊤.

		addW = fmla.MustParseWff("¬□⊥") // ¬□⊥.

		for _, j1 = range js1 {
			if _, pms = prfI.AddLine(addW, pr.DmdIntEw, j1); pms == pr.StatusOK { // ⊢MPL+Ew ¬□⊥.
				tot += 1
			}
		}

		js1 = keepLines(nil, prfI, strIs("◇⊥")) // ◇⊥.

		addW = fmla.MustParseWff("¬□⊤") // ¬□⊤.

		for _, j1 = range js1 {
			if _, pms = prfI.AddLine(addW, pr.DmdIntEw, j1); pms == pr.StatusOK { // ⊢MPL+Ew ¬□⊤.
				tot += 1
			}
		}
	}

	return
}

var ndBoxIntEn ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI *pr.Prf
		js1  []*pr.Line
		j1   *pr.Line
		addW *fmla.Wff
		pms  pr.PrfMutStatus
	)

	// □A ⊢MPL+En ¬◇¬A; □¬A ⊢MPL+En ¬◇A.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		js1 = keepLines(nil, prfI, mopIs(fmla.Box)) // □A.

		for _, j1 = range js1 {
			addW = fmla.MustParseWffFmt("¬◇¬%s", j1.Wff().SubL()) // ¬◇¬A.

			if _, pms = prfI.AddLine(addW, pr.BoxIntEn, j1); pms == pr.StatusOK { // ⊢MPL+En ¬◇¬A.
				tot += 1
			}

			if j1.Wff().SubL().Mop() == fmla.Neg { // □¬A.
				addW = fmla.MustParseWffFmt("¬◇%s", j1.Wff().Locate("LL")) // ¬◇A.

				if _, pms = prfI.AddLine(addW, pr.BoxIntEn, j1); pms == pr.StatusOK { // ⊢MPL+En ¬◇A.
					tot += 1
				}
			}
		}
	}

	return
}

var ndDmdIntEn ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI *pr.Prf
		js1  []*pr.Line
		j1   *pr.Line
		addW *fmla.Wff
		pms  pr.PrfMutStatus
	)

	// ◇A ⊢MPL+En ¬□¬A; ◇¬A ⊢MPL+En ¬□A.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		js1 = keepLines(nil, prfI, mopIs(fmla.Dmd)) // ◇A.

		for _, j1 = range js1 {
			addW = fmla.MustParseWffFmt("¬□¬%s", j1.Wff().SubL()) // ¬□¬A.

			if _, pms = prfI.AddLine(addW, pr.DmdIntEn, j1); pms == pr.StatusOK { // ⊢MPL+En ¬□¬A.
				tot += 1
			}

			if j1.Wff().SubL().Mop() == fmla.Neg { // ◇¬A.
				addW = fmla.MustParseWffFmt("¬□%s", j1.Wff().Locate("LL")) // ¬□A.

				if _, pms = prfI.AddLine(addW, pr.DmdIntEn, j1); pms == pr.StatusOK { // ⊢MPL+En ¬□A.
					tot += 1
				}
			}
		}
	}

	return
}

var ndBoxIntEs ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		js1, js2   []*pr.Line
		j1, j2     *pr.Line
		reqs2      []func(*pr.Line) bool
		addW       *fmla.Wff
		pms        pr.PrfMutStatus
	)

	// If ⊢ A→¬B, □A,A→¬B ⊢MPL+Es ¬◇B.
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistMIs(0)) {
		js1 = keepLines(prfO, prfI, mopIs(fmla.Box)) // □A.

		for _, j1 = range js1 {
			reqs2 = []func(*pr.Line) bool{}
			reqs2 = append(reqs2, mopIs(fmla.To), ruleIs(pr.Thm), subIs("L", j1.Wff().SubL()), subMopIs("R", fmla.Neg))

			js2 = keepLines(prfO, prfI, reqs2...) // ⊢ A→¬B.

			for _, j2 = range js2 {
				addW = fmla.MustParseWffFmt("¬◇%s", j2.Wff().Locate("RL")) // ¬◇B.

				if _, pms = prfI.AddLine(addW, pr.BoxIntEs, j1, j2); pms == pr.StatusOK { // ⊢MPL+Es ¬◇B.
					tot += 1
				}
			}
		}
	}

	return
}

var ndDmdIntEs ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		js1, js2   []*pr.Line
		j1, j2     *pr.Line
		reqs2      []func(*pr.Line) bool
		addW       *fmla.Wff
		pms        pr.PrfMutStatus
	)

	// If ⊢ A→¬B, ◇A,A→¬B ⊢MPL+Es ¬□B.
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistMIs(0)) {
		js1 = keepLines(prfO, prfI, mopIs(fmla.Dmd)) // ◇A.

		for _, j1 = range js1 {
			reqs2 = []func(*pr.Line) bool{}
			reqs2 = append(reqs2, mopIs(fmla.To), ruleIs(pr.Thm), subIs("L", j1.Wff().SubL()), subMopIs("R", fmla.Neg))

			js2 = keepLines(prfO, prfI, reqs2...) // ⊢ A→¬B.

			for _, j2 = range js2 {
				addW = fmla.MustParseWffFmt("¬□%s", j2.Wff().Locate("RL")) // ¬□B.

				if _, pms = prfI.AddLine(addW, pr.DmdIntEs, j1, j2); pms == pr.StatusOK { // ⊢MPL+Es ¬□B.
					tot += 1
				}
			}
		}
	}

	return
}

var ndDmdI ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI *pr.Prf
		js1  []*pr.Line
		j1   *pr.Line
		addW *fmla.Wff
		pms  pr.PrfMutStatus
	)

	// ¬□¬A ⊢CPL+Ew ◇A.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		js1 = keepLines(nil, prfI, mopIs(fmla.Neg), subMopIs("L", fmla.Box), subMopIs("LL", fmla.Neg)) // ¬□¬A.

		for _, j1 = range js1 {
			addW = fmla.NewUnaryWff(fmla.Dmd, j1.Wff().Locate("LLL"))

			if _, pms = prfI.AddLine(addW, pr.DmdI, j1); pms == pr.StatusOK { // ⊢CPL+Ew ◇A.
				tot += 1
			}
		}
	}

	return
}

var ndBoxMon ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI *pr.Prf
		js1  []*pr.Line
		j1   *pr.Line
		addW *fmla.Wff
		pms  pr.PrfMutStatus
	)

	// If ⊢ A→B, then A→B ⊢PPL+M □A→□B.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		js1 = keepLines(nil, prfI, mopIs(fmla.To), ruleIs(pr.Thm))

		for _, j1 = range js1 {
			addW = fmla.MustParseWffFmt("□%s→□%s", j1.Wff().SubL(), j1.Wff().SubR())

			if _, pms = prfI.AddLine(addW, pr.BoxMon, j1); pms == pr.StatusOK { // ⊢PPL+M □A→□B.
				tot += 1
			}
		}
	}

	return
}

var ndDmdMon ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI *pr.Prf
		js1  []*pr.Line
		j1   *pr.Line
		addW *fmla.Wff
		pms  pr.PrfMutStatus
	)

	// If ⊢ A→B, then A→B ⊢PPL+M ◇A→◇B.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		js1 = keepLines(nil, prfI, mopIs(fmla.To), ruleIs(pr.Thm))

		for _, j1 = range js1 {
			addW = fmla.MustParseWffFmt("◇%s→◇%s", j1.Wff().SubL(), j1.Wff().SubR()) // ◇A→◇B.

			if _, pms = prfI.AddLine(addW, pr.DmdMon, j1); pms == pr.StatusOK { // ⊢PPL+M ◇A→◇B.
				tot += 1
			}
		}
	}

	return
}

var ndBoxE ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		j1, j2, j3 *pr.Line
		pms        pr.PrfMutStatus
	)

	// □A,[A…B]□E ⊢PPL+M □B.
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistPIs(1), pr.PurpIs(pr.BoxE)) {
		if j2 = prfI.LineAtIndex(0); j2 == nil || j2.Rule() != pr.Ass { // [A…]□E.
			continue
		}

		j1, _, _, _ = j2.Justs()

		if j3 = prfI.LineWithWff(prfI.WffG()); j3 == nil { // […B]□E.
			continue
		}

		if _, pms = prfO.AddLine(prfI.WffD(), pr.BoxE, j1, j2, j3); pms == pr.StatusOK { // ⊢PPL+M □B.
			tot, _, _ = tot+1, prfI.Close(), prfI.Prune()
		}
	}

	return
}

var ndDmdE ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		j1, j2, j3 *pr.Line
		pms        pr.PrfMutStatus
	)

	// ◇A,[A…B]◇E ⊢PPL+M ◇B.
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistPIs(1), pr.PurpIs(pr.DmdE)) {
		if j2 = prfI.LineAtIndex(0); j2 == nil || j2.Rule() != pr.Ass { // [A…]◇E.
			continue
		}

		j1, _, _, _ = j2.Justs()

		if j3 = prfI.LineWithWff(prfI.WffG()); j3 == nil { // […B]◇E.
			continue
		}

		if _, pms = prfO.AddLine(prfI.WffD(), pr.DmdE, j1, j2, j3); pms == pr.StatusOK { // ⊢PPL+M ◇B.
			tot, _, _ = tot+1, prfI.Close(), prfI.Prune()
		}
	}

	return
}

var ndBoxI ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		j1, j2     *pr.Line
		pms        pr.PrfMutStatus
	)

	// [⊤…A]□I ⊢PPL+N □A.
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistPIs(1), pr.PurpIs(pr.BoxI)) {
		if j1 = prfI.LineAtIndex(0); j1 == nil || j1.Rule() != pr.Ass { // [⊤…]□I.
			continue
		}

		if j2 = prfI.LineWithWff(prfI.WffG()); j2 == nil { // […A]□I.
			continue
		}

		if _, pms = prfO.AddLine(prfI.WffD(), pr.BoxI, j1, j2); pms == pr.StatusOK { // ⊢PPL+N □A.
			tot, _, _ = tot+1, prfI.Close(), prfI.Prune()
		}
	}

	return
}

var ndNegDmdI ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		j1, j2     *pr.Line
		pms        pr.PrfMutStatus
	)

	// [⊤…¬A]¬◇I ⊢MPL+N ¬◇A
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistPIs(1), pr.PurpIs(pr.NegDmdI)) {
		if j1 = prfI.LineAtIndex(0); j1 == nil || j1.Rule() != pr.Ass { // [⊤…]¬◇I.
			continue
		}

		if j2 = prfI.LineWithWff(prfI.WffG()); j2 == nil { // […¬A]¬◇I.
			continue
		}

		if _, pms = prfO.AddLine(prfI.WffD(), pr.NegDmdI, j1, j2); pms == pr.StatusOK { // ⊢MPL+N ¬◇A.
			tot, _, _ = tot+1, prfI.Close(), prfI.Prune()
		}
	}

	return
}

var ndBoxAgg ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI, prfT *pr.Prf
		trg        *fmla.Wff
		js1, js2   []*pr.Line
		j1, j2     *pr.Line
		pms        pr.PrfMutStatus
	)

	// □A,□B ⊢PPL+C □(A∧B).
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		for prfT, trg = range prf.WalkTargets(pr.SeesAll(prfI)) {
			if trg.Mop() != fmla.Box || trg.SubL().Mop() != fmla.Wedge { // □(A∧B).
				continue
			} else if prfT.DistM(prfI)*prfI.DistM(prfT) != 0 {
				continue
			}

			js1 = keepLines(nil, prfI, mopIs(fmla.Box), subIs("L", trg.SubL().SubL())) // □A.

			js2 = keepLines(nil, prfI, mopIs(fmla.Box), subIs("L", trg.SubL().SubR())) // □B.

			for _, j1 = range js1 {
				for _, j2 = range js2 {
					if _, pms = prfI.AddLine(trg, pr.BoxAgg, j1, j2); pms == pr.StatusOK { // ⊢PPL+C □(A∧B).
						tot += 1
					}
				}
			}
		}
	}

	return
}

var ndReitC ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		js1        []*pr.Line
		j1         *pr.Line
		pms        pr.PrfMutStatus
	)

	// □A,[…](□E|□I) ⊢PPL+C […A](□E|□I).
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistMIs(1), pr.PurpIs(pr.BoxE, pr.BoxI)) { // […](□E|□I)
		js1 = keepLines(prfO, nil, mopIs(fmla.Box)) // □A.

		for _, j1 = range js1 {
			if _, pms = prfI.AddLine(j1.Wff().SubL(), pr.ReitC, j1); pms == pr.StatusOK { // ⊢PPL+C […A](□E|□I).
				tot += 1
			}
		}
	}

	return
}

var ndReitK ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfO, prfI *pr.Prf
		js1        []*pr.Line
		j1         *pr.Line
		pms        pr.PrfMutStatus
	)

	// □A,[…]◇E ⊢PPL+K […A]◇E.
	for prfO, prfI = range prf.WalkPrfPairs(pr.DistMIs(1), pr.PurpIs(pr.DmdE)) {
		js1 = keepLines(prfO, nil, mopIs(fmla.Box)) // □A.

		for _, j1 = range js1 {
			if _, pms = prfI.AddLine(j1.Wff().SubL(), pr.ReitK, j1); pms == pr.StatusOK { // ⊢PPL+K “[…A]◇E”.
				tot += 1
			}
		}
	}

	return
}

var ndRuleD ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI *pr.Prf
		js1  []*pr.Line
		j1   *pr.Line
		addW *fmla.Wff
		pms  pr.PrfMutStatus
	)

	// □A ⊢PPL+D ◇A.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		js1 = keepLines(nil, prfI, mopIs(fmla.Box)) // □A.

		for _, j1 = range js1 {
			addW = fmla.NewUnaryWff(fmla.Dmd, j1.Wff().SubL())

			if _, pms = prfI.AddLine(addW, pr.RuleD, j1); pms == pr.StatusOK { // ⊢PPL+D ◇A.
				tot += 1
			}
		}
	}

	return
}

var ndIntroT ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI, prfT *pr.Prf
		trg        *fmla.Wff
		js1        []*pr.Line
		j1         *pr.Line
		pms        pr.PrfMutStatus
	)

	// A ⊢PPL+T ◇A.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		for prfT, trg = range prf.WalkTargets(pr.SeesAll(prfI)) {
			if trg.Mop() != fmla.Dmd || prfT.DistM(prfI)*prfI.DistM(prfT) != 0 {
				continue
			}

			js1 = keepLines(nil, prfI, wffIs(trg.SubL())) // A.

			for _, j1 = range js1 {
				if _, pms = prfI.AddLine(trg, pr.IntroT, j1); pms == pr.StatusOK { // ⊢PPL+T ◇A.
					tot += 1
				}
			}
		}
	}

	return
}

var ndElimT ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI *pr.Prf
		js1  []*pr.Line
		j1   *pr.Line
		pms  pr.PrfMutStatus
	)

	// □A ⊢PPL+T A.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		js1 = keepLines(nil, prfI, mopIs(fmla.Box)) // □A.

		for _, j1 = range js1 {
			if _, pms = prfI.AddLine(j1.Wff().SubL(), pr.ElimT, j1); pms == pr.StatusOK { // ⊢PPL+T A.
				tot += 1
			}
		}
	}

	return
}

var ndIntro4 ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI, prfT *pr.Prf
		trg        *fmla.Wff
		js1        []*pr.Line
		j1         *pr.Line
		pms        pr.PrfMutStatus
	)

	// □A ⊢PPL+4 □□A.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		for prfT, trg = range prf.WalkTargets(pr.SeesAll(prfI)) {
			if trg.Mop() != fmla.Box || trg.SubL().Mop() != fmla.Box || prfT.DistM(prfI)*prfI.DistM(prfT) != 0 { // □□A.
				continue
			}

			js1 = keepLines(nil, prfI, wffIs(trg.SubL())) // □A.

			for _, j1 = range js1 {
				if _, pms = prfI.AddLine(trg, pr.Intro4, j1); pms == pr.StatusOK { // ⊢PPL+4 □□A.
					tot += 1
				}
			}
		}
	}

	return
}

var ndElim4 ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI *pr.Prf
		js1  []*pr.Line
		j1   *pr.Line
		pms  pr.PrfMutStatus
	)

	// ◇◇A ⊢PPL+4 ◇A.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		js1 = keepLines(nil, prfI, mopIs(fmla.Dmd), subMopIs("L", fmla.Dmd)) // ◇◇A.

		for _, j1 = range js1 {
			if _, pms = prfI.AddLine(j1.Wff().SubL(), pr.Elim4, j1); pms == pr.StatusOK { // ⊢PPL+4 ◇A.
				tot += 1
			}
		}
	}

	return
}

var ndIntroB ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI, prfT *pr.Prf
		trg        *fmla.Wff
		js1        []*pr.Line
		j1         *pr.Line
		pms        pr.PrfMutStatus
	)

	// A ⊢PPL+B □◇A.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		for prfT, trg = range prf.WalkTargets(pr.SeesAll(prfI)) {
			if trg.Mop() != fmla.Box || trg.SubL().Mop() != fmla.Dmd || prfT.DistM(prfI)*prfI.DistM(prfT) != 0 { // □◇A.
				continue
			}

			js1 = keepLines(nil, prfI, wffIs(trg.Locate("LL"))) // A.

			for _, j1 = range js1 {
				if _, pms = prfI.AddLine(trg, pr.IntroB, j1); pms == pr.StatusOK { // ⊢PPL+B □◇A.
					tot += 1
				}
			}
		}
	}

	return
}

var ndElimB ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI *pr.Prf
		js1  []*pr.Line
		j1   *pr.Line
		pms  pr.PrfMutStatus
	)

	// ◇□A ⊢PPL+B A.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		js1 = keepLines(nil, prfI, mopIs(fmla.Dmd), subMopIs("L", fmla.Box)) // ◇□A.

		for _, j1 = range js1 {
			if _, pms = prfI.AddLine(j1.Wff().SubL().SubL(), pr.ElimB, j1); pms == pr.StatusOK { // ⊢PPL+B A.
				tot += 1
			}
		}
	}

	return
}

var ndIntro5 ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI, prfT *pr.Prf
		trg        *fmla.Wff
		js1        []*pr.Line
		j1         *pr.Line
		pms        pr.PrfMutStatus
	)

	// ◇A ⊢PPL+5 □◇A.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		for prfT, trg = range prf.WalkTargets(pr.SeesAll(prfI)) {
			if trg.Mop() != fmla.Box || trg.SubL().Mop() != fmla.Dmd || prfT.DistM(prfI)*prfI.DistM(prfT) != 0 { // □◇A.
				continue
			}

			js1 = keepLines(nil, prfI, wffIs(trg.SubL())) // ◇A.

			for _, j1 = range js1 {
				if _, pms = prfI.AddLine(trg, pr.Intro5, j1); pms == pr.StatusOK { // ⊢PPL+5 □◇A.
					tot += 1
				}
			}
		}
	}

	return
}

var ndElim5 ndRuleFunc = func(prf *pr.Prf) (tot int) {
	var (
		prfI *pr.Prf
		js1  []*pr.Line
		j1   *pr.Line
		pms  pr.PrfMutStatus
	)

	// ◇□A ⊢PPL+5 □A.
	for prfI = range prf.WalkPrfPairs(pr.DistPIs(0)) {
		js1 = keepLines(nil, prfI, mopIs(fmla.Dmd), subMopIs("L", fmla.Box)) // ◇□A.

		for _, j1 = range js1 {
			if _, pms = prfI.AddLine(j1.Wff().SubL(), pr.Elim5, j1); pms == pr.StatusOK { // ⊢PPL+5 □A.
				tot += 1
			}
		}
	}

	return
}

var ruleToFunc map[pr.NDRule]ndRuleFunc = map[pr.NDRule]ndRuleFunc{
	pr.TopI:     ndTopI,
	pr.ToI:      ndToI,
	pr.ToE:      ndToE,
	pr.Reit:     ndReit,
	pr.Thm:      ndThm,
	pr.WedgeI:   ndWedgeI,
	pr.WedgeE:   ndWedgeE,
	pr.VeeI:     ndVeeI,
	pr.VeeE:     ndVeeE,
	pr.IffI:     ndIffI,
	pr.IffE:     ndIffE,
	pr.BotI:     ndBotI,
	pr.BotE:     ndBotE,
	pr.NegI:     ndNegI,
	pr.NegE:     ndNegE,
	pr.Jan:      ndJan,
	pr.Göd:      ndGöd,
	pr.Sme:      ndSme,
	pr.EqualI:   ndEqualI,
	pr.EqualE:   ndEqualE,
	pr.ForAllI:  ndForAllI,
	pr.ForAllE:  ndForAllE,
	pr.ExistsI:  ndExistsI,
	pr.ExistsE:  ndExistsE,
	pr.BoxCon:   ndBoxCon,
	pr.DmdCon:   ndDmdCon,
	pr.BoxIntEw: ndBoxIntEw,
	pr.DmdIntEw: ndDmdIntEw,
	pr.BoxIntEn: ndBoxIntEn,
	pr.DmdIntEn: ndDmdIntEn,
	pr.BoxIntEs: ndBoxIntEs,
	pr.DmdIntEs: ndDmdIntEs,
	pr.DmdI:     ndDmdI,
	pr.BoxMon:   ndBoxMon,
	pr.DmdMon:   ndDmdMon,
	pr.BoxE:     ndBoxE,
	pr.DmdE:     ndDmdE,
	pr.BoxI:     ndBoxI,
	pr.NegDmdI:  ndNegDmdI,
	pr.BoxAgg:   ndBoxAgg,
	pr.ReitC:    ndReitC,
	pr.ReitK:    ndReitK,
	pr.RuleD:    ndRuleD,
	pr.IntroT:   ndIntroT,
	pr.ElimT:    ndElimT,
	pr.Intro4:   ndIntro4,
	pr.Elim4:    ndElim4,
	pr.IntroB:   ndIntroB,
	pr.ElimB:    ndElimB,
	pr.Intro5:   ndIntro5,
	pr.Elim5:    ndElim5,
}
