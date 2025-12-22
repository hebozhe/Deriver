package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
)

type NDIntroFunc func(prf *pr.Proof) (stepsD []*pr.Step, lenD int)

type NDElimFunc func(prf *pr.Proof) (stepsD []*pr.Step, needsD []*fmla.WffTree, lenD int)

func Derive(goal *fmla.WffTree, pwffs ...*fmla.WffTree) (prf *pr.Proof) {
	prf = pr.NewBaseProof(goal, pwffs...)

	return
}
