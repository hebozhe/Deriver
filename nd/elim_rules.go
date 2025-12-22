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
		stepsL                                   []*Step
		wD                                       World
		p1, p2, p3                               *Step
		p1L, p1R, p2L, p2R, p3L, p3R, goal, wffN *fmla.WffTree
		con                                      fmla.Connective
		stepD                                    *Step
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

		for _, goal = range prf.goals {
			wffN = fmla.NewConnectiveWff(fmla.To, p1L, goal)

			needsD = append(needsD, wffN)
		}
	}

	return
}

var doIffElim NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	var (
		stepsL         []*Step
		wD             World
		p1             *Step
		p1L, p1R, wffD *fmla.WffTree
		con            fmla.Connective
		stepD          *Step
	)

	stepsL = GetSteps(prf, LegalScope)

	wD = GetWorldAtPoof(prf)

	for _, p1 = range stepsL {
		if con, _, _ = fmla.GetWffMainOperator(p1.wff); con != fmla.Iff {
			continue
		}

		p1L, p1R, _ = fmla.GetWffSubformulae(p1.wff)

		wffD = fmla.NewConnectiveWff(fmla.To, p1L, p1R)

		stepD = NewStep(wffD, wD, IffElim, 0, p1)

		stepsD = append(stepsD, stepD)

		wffD = fmla.NewConnectiveWff(fmla.To, p1R, p1L)

		stepD = NewStep(wffD, wD, IffElim, 0, p1)

		stepsD = append(stepsD, stepD)
	}

	return
}

var doBotElim NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	var (
		Fwff  *fmla.WffTree
		steps []*Step
		p1    *Step
		wffD  *fmla.WffTree
		wD    World
		stepD *Step
	)

	Fwff = fmla.NewAtomicWff(fmla.Bot)

	steps = GetSteps(prf, LegalScope)

	for _, p1 = range steps {
		if !fmla.Identical(p1.wff, Fwff) {
			continue
		}

		wD = GetWorld(p1)

		for _, wffD = range prf.goals {
			stepD = NewStep(wffD, wD, BotElim, 0, p1)

			stepsD = append(stepsD, stepD)

			break
		}

		break
	}

	return
}

var doNegElim NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	var (
		steps      []*Step
		p1         *Step
		p1L        *fmla.WffTree
		conX, conY fmla.Connective
		wD         World
		stepD      *Step
	)

	steps = GetSteps(prf, LegalScope)

	for _, p1 = range steps {
		if conX, _, _ = fmla.GetWffMainOperator(p1.wff); conX != fmla.Neg {
			continue
		}

		p1L, _, _ = fmla.GetWffSubformulae(p1.wff)

		if conY, _, _ = fmla.GetWffMainOperator(p1L); conY != fmla.Neg {
			continue
		}

		p1L, _, _ = fmla.GetWffSubformulae(p1L)

		wD = GetWorld(p1)

		stepD = NewStep(p1L, wD, NegElim, 0, p1)

		stepsD = append(stepsD, stepD)
	}

	return
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
	var (
		stepsL []*Step
		wD     World
		p1     *Step
		p1L    *fmla.WffTree
		con    fmla.Connective
		stepD  *Step
	)

	wD = GetWorldAtPoof(prf)

	stepsL = GetSteps(prf, LegalScope)

	for _, p1 = range stepsL {
		if con, _, _ = fmla.GetWffMainOperator(p1.wff); con != fmla.Box {
			continue
		}

		p1L, _, _ = fmla.GetWffSubformulae(p1.wff)

		stepD = NewStep(p1L, wD, BoxElim, 0, p1)

		stepsD = append(stepsD, stepD)
	}

	return
}

var doDiamondElim NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	panic("Not implemented")
}

var doElimM NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	var (
		steps []*Step
		p1    *Step
		p1L   *fmla.WffTree
		con   fmla.Connective
		wD    World
		stepD *Step
	)

	steps = GetSteps(prf, LegalScope)

	for _, p1 = range steps {
		if con, _, _ = fmla.GetWffMainOperator(p1.wff); con != fmla.Box {
			continue
		}

		p1L, _, _ = fmla.GetWffSubformulae(p1.wff)

		wD = GetWorld(p1)

		stepD = NewStep(p1L, wD, ElimM, 0, p1)

		stepsD = append(stepsD, stepD)
	}

	return
}

var doElim4 NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	var (
		steps []*Step
		p1    *Step
		p1L   *fmla.WffTree
		con   fmla.Connective
		wD    World
		stepD *Step
	)

	steps = GetSteps(prf, LegalScope)

	for _, p1 = range steps {
		if con, _, _ = fmla.GetWffMainOperator(p1.wff); con != fmla.Diamond {
			continue
		}

		p1L, _, _ = fmla.GetWffSubformulae(p1.wff)

		if con, _, _ = fmla.GetWffMainOperator(p1L); con != fmla.Diamond {
			continue
		}

		stepD = NewStep(p1L, wD, Elim4, 0, p1)

		stepsD = append(stepsD, stepD)
	}

	return
}

var doElimB NDElimFunc = func(prf *Proof) (stepsD []*Step, needsD []*fmla.WffTree) {
	var (
		steps []*Step
		p1    *Step
		p1L   *fmla.WffTree
		con   fmla.Connective
		wD    World
		stepD *Step
	)

	steps = GetSteps(prf, LegalScope)

	for _, p1 = range steps {
		if con, _, _ = fmla.GetWffMainOperator(p1.wff); con != fmla.Diamond {
			continue
		}

		p1L, _, _ = fmla.GetWffSubformulae(p1.wff)

		if con, _, _ = fmla.GetWffMainOperator(p1L); con != fmla.Box {
			continue
		}

		p1L, _, _ = fmla.GetWffSubformulae(p1L)

		wD = GetWorld(p1)

		stepD = NewStep(p1L, wD, ElimB, 0, p1)

		stepsD = append(stepsD, stepD)
	}

	return
}
