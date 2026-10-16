package pr

import (
	"slices"
)

type prfCrit func(prfO *Prf, prfI *Prf) (met, kill bool)

func DistPIs(distP int) (critP prfCrit) {
	critP = func(prfO *Prf, prfI *Prf) (met, kill bool) {
		if met = prfI.depthP-prfO.depthP == distP; !met {
			kill = distP < prfI.depthP-prfO.depthP
		}

		return
	}

	return
}

func DistMIs(distM int) (critP prfCrit) {
	critP = func(prfO *Prf, prfI *Prf) (met, kill bool) {
		if met = prfI.depthM-prfO.depthM == distM; !met {
			kill = distM < prfI.depthM-prfO.depthM
		}

		return
	}

	return
}

func SeesAll(prfs ...*Prf) (critP prfCrit) {
	var base []*Prf

	if InnermostProof(prfs...) == nil {
		panic("Input proofs must be mutually comparable.")
	}

	base = slices.Clone(prfs)

	critP = func(prfO *Prf, prfI *Prf) (met, kill bool) {
		var (
			baseO, baseI []*Prf
		)

		baseO, baseI = append(slices.Clone(base), prfO), append(slices.Clone(base), prfI)

		met = InnermostProof(baseO...) != nil && InnermostProof(baseI...) != nil

		return
	}
	return
}

func PurpIs(purps ...NDRule) (critP prfCrit) {
	critP = func(_ *Prf, prfI *Prf) (met, kill bool) {
		met = slices.Contains(purps, prfI.purp)

		kill = !met

		return
	}

	return
}
