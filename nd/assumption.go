package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
)

func (drv *Derivation) pushAssumptions(wffG *fmla.WffTree, prf *pr.Proof) (tot int) {
	var (
		mopI fmla.Symbol
	)

	mopI = fmla.GetWffMop(wffG)

	switch mopI {
	case fmla.NoSymbol:
		if pr.Intuitionistic < drv.InfS { // At least Classical...
			var (
				wff, bot *fmla.WffTree
				prfI     *pr.Proof
			)

			wff = fmla.NewCompositeWff(fmla.Neg, wffG, nil, 0, 0)

			bot = fmla.NewAtomicWff(fmla.Bot)

			if !fmla.IsIdentical(wffG, bot) {
				_, prfI = pr.NewLine(wff, bot, pr.Assumption, pr.NegIntro, prf)

				tot += prf.InsertInnerProof(prfI)
			}
		}
	case fmla.Neg:
		if pr.Positive < drv.InfS { // At least Minimal...
			var (
				subL, bot *fmla.WffTree
				prfI      *pr.Proof
			)

			subL, _ = fmla.GetWffSubformulae(wffG)

			bot = fmla.NewAtomicWff(fmla.Bot)

			_, prfI = pr.NewLine(subL, bot, pr.Assumption, pr.NegIntro, prf)

			tot += prf.InsertInnerProof(prfI)
		}
	case fmla.Wedge:
		if pr.Implicational < drv.InfS { // At least Positive...
			var (
				subL, subR *fmla.WffTree
			)

			subL, subR = fmla.GetWffSubformulae(wffG)

			tot += drv.pushAssumptions(subL, prf) + drv.pushAssumptions(subR, prf)
		}
	case fmla.Vee:
		if pr.Implicational < drv.InfS { // At least Positive...
			var (
				subL, subR *fmla.WffTree
			)

			subL, subR = fmla.GetWffSubformulae(wffG)

			tot += drv.pushAssumptions(subL, prf)
			tot += drv.pushAssumptions(subR, prf)
		}

		if pr.Intuitionistic < drv.InfS { // At least Classical...
			var (
				wff, bot *fmla.WffTree
				prfI     *pr.Proof
			)

			wff = fmla.NewCompositeWff(fmla.Neg, wffG, nil, 0, 0)

			bot = fmla.NewAtomicWff(fmla.Bot)

			_, prfI = pr.NewLine(wff, bot, pr.Assumption, pr.NegIntro, prf)

			tot += prf.InsertInnerProof(prfI)
		}
	case fmla.To:
		if pr.NoInference < drv.InfS { // At least Implicational...
			var (
				subL, subR *fmla.WffTree
				prfI       *pr.Proof
			)

			subL, subR = fmla.GetWffSubformulae(wffG)

			_, prfI = pr.NewLine(subL, subR, pr.Assumption, pr.ToIntro, prf)

			tot += prf.InsertInnerProof(prfI)
			tot += drv.pushAssumptions(subR, prfI)
		}
	case fmla.Iff:
		if pr.Implicational < drv.InfS { // At least Positive...
			var (
				subL, subR *fmla.WffTree
				prfI       *pr.Proof
			)

			subL, subR = fmla.GetWffSubformulae(wffG)

			_, prfI = pr.NewLine(subL, subR, pr.Assumption, pr.ToIntro, prf)

			tot += prf.InsertInnerProof(prfI)
			tot += drv.pushAssumptions(subR, prfI)

			_, prfI = pr.NewLine(subR, subL, pr.Assumption, pr.ToIntro, prf)

			tot += prf.InsertInnerProof(prfI)
			tot += drv.pushAssumptions(subL, prfI)
		}
	case fmla.ForAll:
		if pr.Implicational < drv.InfS { // At least Positive...
			var (
				pv, apc  fmla.Predicate
				av, aac  fmla.Argument
				top, wff *fmla.WffTree
				prfI     *pr.Proof
			)

			pv, av = fmla.GetWffVars(wffG)

			_, _, apc, aac = prf.GetLocalConstants()

			top = fmla.NewAtomicWff(fmla.Top)

			switch {
			case pv != 0 && apc != 0:
				wff = fmla.Instantiate(wffG, apc, 0)
			case av != 0 && aac != 0:
				wff = fmla.Instantiate(wffG, 0, aac)
			default:
				panic("No instantiation is possible.")
			}

			_, prfI = pr.NewLine(top, wff, pr.Assumption, pr.ForAllIntro, prf)

			tot += prf.InsertInnerProof(prfI)

			tot += drv.pushAssumptions(wff, prfI)
		}
	case fmla.Exists:
		if pr.Implicational < drv.InfS { // At least Positive...
		}
	case fmla.Box:
		if pr.Implicational < drv.InfS { // At least Positive...
			var (
				prfI     *pr.Proof
				top, wff *fmla.WffTree
			)

			top = fmla.NewAtomicWff(fmla.Top)

			wff, _ = fmla.GetWffSubformulae(wffG)

			_, prfI = pr.NewLine(top, wff, pr.Assumption, pr.BoxIntro, prf)

			tot += prf.InsertInnerProof(prfI)

			tot += drv.pushAssumptions(wff, prfI)
		}

		if pr.IsAllowedModality(pr.IntroK, drv.ModS) {
			var (
				prfO *pr.Proof
				wff  *fmla.WffTree
			)

			prfO = prf.GetOutermostProof()

			wff, _ = fmla.GetWffSubformulae(wffG)

			tot += drv.pushAssumptions(wff, prfO)
		}
	case fmla.Diamond:
		if pr.Intuitionistic < drv.InfS { // At least Classical...
			var (
				prfI     *pr.Proof
				wff, bot *fmla.WffTree
			)

			wff, _ = fmla.GetWffSubformulae(wffG)
			wff = fmla.NewUnaryChainWff([]fmla.Symbol{fmla.Box, fmla.Neg}, wff)

			bot = fmla.NewAtomicWff(fmla.Bot)

			_, prfI = pr.NewLine(wff, bot, pr.Assumption, pr.NegIntro, prf)

			tot += prf.InsertInnerProof(prfI)
		}
	}

	return
}

func (drv *Derivation) helpDistributions() (tot int) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
		lis   []*pr.LineInfo
		li    *pr.LineInfo
		kind  fmla.WffKind
		wff   *fmla.WffTree
	)

	prfsI = drv.Prf.GetInnerProofs(true)
	prfsI = append(prfsI, drv.Prf)

	for _, prfI = range prfsI {
		lis, _ = prfI.GetLocalLines()

		for _, li = range lis {
			if kind = fmla.GetWffKind(li.Wff); kind == fmla.Unary || kind == fmla.Quantified {
				if wff = distributeWff(li.Wff, drv.InfS, drv.ModS); fmla.IsIdentical(wff, li.Wff) {
					continue
				}

				tot += drv.pushAssumptions(wff, prfI)
			}
		}
	}

	return
}

func (drv *Derivation) helpEliminations() (tot int) {
	var (
		prfsI []*pr.Proof
		prfI  *pr.Proof
		lis   []*pr.LineInfo
		li    *pr.LineInfo
	)

	prfsI = drv.Prf.GetInnermostProofs(true)

HELPELIMINATIONS_OUTER:
	for _, prfI = range prfsI {
		lis, _ = prfI.GetLegalLines()

		for _, li = range lis {
			switch li.Mop {
			case fmla.NoSymbol:
				// So far, there are no needed rules.
			case fmla.Neg:
				var (
					subL, bot, wff *fmla.WffTree
				)

				subL, _ = fmla.GetWffSubformulae(li.Wff)

				bot = fmla.NewAtomicWff(fmla.Bot)

				wff = fmla.NewCompositeWff(fmla.To, subL, bot, 0, 0)

				tot += drv.pushAssumptions(wff, li.Prf)
			case fmla.Wedge:
				// Single-premise rule, do nothing.
			case fmla.Vee:
				var (
					wff, wffG *fmla.WffTree
				)

				wff = prfI.GetWffG()

				wffG = fmla.NewCompositeWff(fmla.To, li.SubL, wff, 0, 0)

				tot += drv.pushAssumptions(wffG, prfI)

				wffG = fmla.NewCompositeWff(fmla.To, li.SubR, wff, 0, 0)

				tot += drv.pushAssumptions(wffG, prfI)
			case fmla.To:
				tot += drv.pushAssumptions(li.SubL, prfI)
			case fmla.Iff:
				// Single-premise rule, do nothing.
			case fmla.ForAll:
				// Single-premise rule, do nothing.
			case fmla.Exists:
				var (
					prfsI      []*pr.Proof
					prf, prfII *pr.Proof
					li0        *pr.LineInfo
					apc        fmla.Predicate
					aac        fmla.Argument
					wff, wffG  *fmla.WffTree
				)

				if li.Rule == pr.ExistsIntro || li.Rule == pr.Reiteration {
					continue HELPELIMINATIONS_OUTER
				}

				// Check if we are already eliminating this existential formula.
				prfsI = prfI.GetInnerProofs(true)

				for _, prf = range prfsI {
					if li0 = prf.GetFirstLine(); prf.GetPurpose() == pr.ExistsElim && li0.J1 == li.Ln {
						continue HELPELIMINATIONS_OUTER
					}
				}

				_, _, apc, aac = prfI.GetLegalConstants()

				if li.PV != 0 {
					wff = fmla.Instantiate(li.Wff, apc, 0)
				} else if li.AV != 0 {
					wff = fmla.Instantiate(li.Wff, 0, aac)
				}

				wffG = prfI.GetWffG()

				_, prfII = pr.NewLine(wff, wffG, pr.Assumption, pr.ExistsElim, prfI, li.Ln)

				tot += prfI.InsertInnerProof(prfII)
			case fmla.Box:
				// Single-premise rule, do nothing.
			case fmla.Diamond:
				var (
					prf, prfII *pr.Proof
					li0        *pr.LineInfo
					wff, wffG  *fmla.WffTree
				)

				if li.Rule == pr.DiamondElim || li.Rule == pr.Reiteration {
					continue HELPELIMINATIONS_OUTER
				}

				// Check if we are already eliminating this diamond formula.
				prfsI = prfI.GetInnerProofs(true)

				for _, prf = range prfsI {
					if li0 = prf.GetFirstLine(); prf.GetPurpose() == pr.DiamondElim && li0.J1 == li.Ln {
						continue HELPELIMINATIONS_OUTER
					}
				}

				wff, _ = fmla.GetWffSubformulae(li.Wff)

				wffG = prfI.GetWffG()

				_, prfII = pr.NewLine(wff, wffG, pr.Assumption, pr.DiamondElim, prfI, li.Ln)

				tot += prfI.InsertInnerProof(prfII)
			}
		}
	}

	return
}
