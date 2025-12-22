package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
)

var doTopIntro NDIntroFunc = func(prf *pr.Proof) (stepsD []*pr.Step, lenD int) {
	var (
		wffD  *fmla.WffTree
		wD    pr.World
		stepD *pr.Step
	)

	wffD = fmla.NewAtomicWff(fmla.Top)

	wD = pr.GetWorldAtPoof(prf)

	stepD = pr.NewStep(wffD, wD, pr.TopIntro, 0)

	stepsD = append(stepsD, stepD)

	lenD = 1

	return
}

var doToIntro NDIntroFunc = func(prf *pr.Proof) (stepsD []*pr.Step, lenD int) {
	panic("Not implemented")
}

var doWedgeIntro NDIntroFunc = func(prf *pr.Proof) (stepsD []*pr.Step, lenD int) {
	panic("Not implemented")
}

var doVeeIntro NDIntroFunc = func(prf *pr.Proof) (stepsD []*pr.Step, lenD int) {
	panic("Not implemented")
}

var doIffIntro NDIntroFunc = func(prf *pr.Proof) (stepsD []*pr.Step, lenD int) {
	panic("Not implemented")
}

var doReit NDIntroFunc = func(prf *pr.Proof) (stepsD []*pr.Step, lenD int) {
	panic("Not implemented")
}

var doBotIntro NDIntroFunc = func(prf *pr.Proof) (stepsD []*pr.Step, lenD int) {
	panic("Not implemented")
}

var doNegIntro NDIntroFunc = func(prf *pr.Proof) (stepsD []*pr.Step, lenD int) {
	panic("Not implemented")
}

var doForAllIntro NDIntroFunc = func(prf *pr.Proof) (stepsD []*pr.Step, lenD int) {
	panic("Not implemented")
}

var doExistsIntro NDIntroFunc = func(prf *pr.Proof) (stepsD []*pr.Step, lenD int) {
	panic("Not implemented")
}

var doIdenIntro NDIntroFunc = func(prf *pr.Proof) (stepsD []*pr.Step, lenD int) {
	panic("Not implemented")
}

var doBoxIntro NDIntroFunc = func(prf *pr.Proof) (stepsD []*pr.Step, lenD int) {
	panic("Not implemented")
}

var doDiamondIntro NDIntroFunc = func(prf *pr.Proof) (stepsD []*pr.Step, lenD int) {
	panic("Not implemented")
}

var doRuleD NDIntroFunc = func(prf *pr.Proof) (stepsD []*pr.Step, lenD int) {
	panic("Not implemented")
}

var doIntroM NDIntroFunc = func(prf *pr.Proof) (stepsD []*pr.Step, lenD int) {
	panic("Not implemented")
}

var doIntro4 NDIntroFunc = func(prf *pr.Proof) (stepsD []*pr.Step, lenD int) {
	panic("Not implemented")
}

var doIntroB NDIntroFunc = func(prf *pr.Proof) (stepsD []*pr.Step, lenD int) {
	panic("Not implemented")
}
