package pr

import (
	"Deriver/fmla"
)

func NewProof(wffG *fmla.Wff, wffsP ...*fmla.Wff) (prf *Prf) {
	var (
		wffP *fmla.Wff
	)

	if wffG == nil {
		panic("Nil goals are not allowed.")
	}

	prf = &Prf{
		wffG:    wffG.DeepCopy(),
		wffD:    wffG.DeepCopy(),
		depthP:  0,
		depthM:  0,
		purp:    Solve,
		open:    true,
		lns:     []*Line{},
		prfO:    nil,
		prfsI:   []*Prf{},
		freshPC: fmla.NoPred, // Only populated when a subproof calls for one.
		freshAC: fmla.NoArg,  // Only populated when a subproof calls for one.
	}

	// Add a vacuous line whose wff is of the form ⊤
	// to ensure that the base proof is non-empty and that its first line is always of the same form.
	prf.lns = []*Line{{wff: fmla.NewAtomicWff(fmla.Top), rule: TopI, prf: prf}}

	for _, wffP = range wffsP {
		if wffP == nil {
			panic("Nil premises are not allowed.")
		}

		_, _ = prf.AddLine(wffP, Prem)
	}

	return
}
