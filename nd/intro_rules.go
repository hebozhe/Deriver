package nd

import (
	"Deriver/fmla"
)

type NDIntroFunc func(prf *Proof) (stepsD []*Step)

var doTopIntro NDIntroFunc = func(prf *Proof) (stepsD []*Step) {
	var (
		wffD  *fmla.WffTree
		wD    World
		stepD *Step
	)

	wffD = fmla.NewAtomicWff(fmla.Top)

	wD = GetWorldAtPoof(prf)

	stepD = NewStep(wffD, wD, TopIntro, 0)

	stepsD = append(stepsD, stepD)

	return
}

var doToIntro NDIntroFunc = func(prf *Proof) (stepsD []*Step) {
	panic("Not implemented")
}

var doWedgeIntro NDIntroFunc = func(prf *Proof) (stepsD []*Step) {
	panic("Not implemented")
}

var doVeeIntro NDIntroFunc = func(prf *Proof) (stepsD []*Step) {
	panic("Not implemented")
}

var doIffIntro NDIntroFunc = func(prf *Proof) (stepsD []*Step) {
	panic("Not implemented")
}

var doReit NDIntroFunc = func(prf *Proof) (stepsD []*Step) {
	panic("Not implemented")
}

var doBotIntro NDIntroFunc = func(prf *Proof) (stepsD []*Step) {
	panic("Not implemented")
}

var doNegIntro NDIntroFunc = func(prf *Proof) (stepsD []*Step) {
	panic("Not implemented")
}

var doForAllIntro NDIntroFunc = func(prf *Proof) (stepsD []*Step) {
	panic("Not implemented")
}

var doExistsIntro NDIntroFunc = func(prf *Proof) (stepsD []*Step) {
	panic("Not implemented")
}

var doIdenIntro NDIntroFunc = func(prf *Proof) (stepsD []*Step) {
	panic("Not implemented")
}

var doBoxIntro NDIntroFunc = func(prf *Proof) (stepsD []*Step) {
	panic("Not implemented")
}

var doDiamondIntro NDIntroFunc = func(prf *Proof) (stepsD []*Step) {
	panic("Not implemented")
}

var doRuleD NDIntroFunc = func(prf *Proof) (stepsD []*Step) {
	panic("Not implemented")
}

var doIntroM NDIntroFunc = func(prf *Proof) (stepsD []*Step) {
	panic("Not implemented")
}

var doIntro4 NDIntroFunc = func(prf *Proof) (stepsD []*Step) {
	panic("Not implemented")
}

var doIntroB NDIntroFunc = func(prf *Proof) (stepsD []*Step) {
	panic("Not implemented")
}
