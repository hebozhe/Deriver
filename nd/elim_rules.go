package nd

import (
	"Deriver/fmla"
)

type NDElimFunc func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree)

var doToElim NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	var (
		stepsL   []*Step
		wD       World
		p1, p2   *Step
		p1L, p1R *fmla.WffTree
		con      fmla.Connective
		stepD    *Step
	)

	stepsL = GetSteps(prf, LegalScope)

	wD = GetWorldAtPoof(prf)

DOTOELIM_OUTER:
	for _, p1 = range stepsL {
		if con, _, _ = fmla.GetWffMainOperator(p1.wff); con != fmla.To {
			continue
		}

		p1L, p1R, _ = fmla.GetWffSubformulae(p1.wff)

		for _, p2 = range stepsL {
			if fmla.Identical(p2.wff, p1L) {
				stepD = NewStep(p1R, wD, ToElim, 0, p1, p2)

				stepsD = append(stepsD, stepD)

				continue DOTOELIM_OUTER
			}
		}

		needsD = append(needsD, p1L)
	}

	return
}

var doWedgeElim NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	var (
		stepsL   []*Step
		wD       World
		p1       *Step
		p1L, p1R *fmla.WffTree
		con      fmla.Connective
		stepD    *Step
	)

	stepsL = GetSteps(prf, LegalScope)

	wD = GetWorldAtPoof(prf)

	for _, p1 = range stepsL {
		if con, _, _ = fmla.GetWffMainOperator(p1.wff); con != fmla.Wedge {
			continue
		}

		p1L, p1R, _ = fmla.GetWffSubformulae(p1.wff)

		stepD = NewStep(p1L, wD, WedgeElim, 0, p1)

		stepsD = append(stepsD, stepD)

		stepD = NewStep(p1R, wD, WedgeElim, 0, p1)

		stepsD = append(stepsD, stepD)
	}

	return
}

var doVeeElim NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	var (
		stepsL                             []*Step
		wD                                 World
		p1, p2, p3                         *Step
		p1L, p1R, p2L, p2R, p3L, p3R, wffN *fmla.WffTree
		con                                fmla.Connective
		stepD                              *Step
	)

	stepsL = GetSteps(prf, LegalScope)

	wD = GetWorldAtPoof(prf)

DOVEEELIM_OUTER:
	for _, p1 = range stepsL {
		if con, _, _ = fmla.GetWffMainOperator(p1.wff); con != fmla.Vee {
			continue
		}

		p1L, p1R, _ = fmla.GetWffSubformulae(p1.wff)

		for _, p2 = range stepsL {
			if con, _, _ = fmla.GetWffMainOperator(p2.wff); con != fmla.To {
				continue
			}

			if p2L, _, _ = fmla.GetWffSubformulae(p2.wff); !fmla.Identical(p2L, p1L) {
				continue
			}

			for _, p3 = range stepsL {
				if con, _, _ = fmla.GetWffMainOperator(p3.wff); con != fmla.To {
					continue
				}

				if p3L, p3R, _ = fmla.GetWffSubformulae(p3.wff); !fmla.Identical(p3L, p1R) {
					continue
				}

				if !fmla.Identical(p2R, p3R) {
					continue
				}

				stepD = NewStep(p2R, wD, VeeElim, 0, p1, p2, p3)

				stepsD = append(stepsD, stepD)

				continue DOVEEELIM_OUTER
			}

			wffN = fmla.NewConnectiveWff(fmla.To, p1R, prf.goals[0])

			needsD = append(needsD, wffN)

			continue DOVEEELIM_OUTER
		}

		wffN = fmla.NewConnectiveWff(fmla.To, p1L, prf.goals[0])

		needsD = append(needsD, wffN)
	}

	return
}

var doIffElim NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {

	return
}

var doBotElim NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	panic("Not implemented")
}

var doNegElim NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	panic("Not implemented")
}

var doForAllElim NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	panic("Not implemented")
}

var doExistsElim NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	panic("Not implemented")
}

var doIdenElim NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	panic("Not implemented")
}

var doBoxElim NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	panic("Not implemented")
}

var doDiamondElim NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	panic("Not implemented")
}

var doElimM NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	panic("Not implemented")
}

var doElim4 NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	panic("Not implemented")
}

var doElimB NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	panic("Not implemented")
}
