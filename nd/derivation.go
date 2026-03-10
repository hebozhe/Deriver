package nd

import (
	"Deriver/nd/pr"
)

type Derivation struct {
	Prf  *pr.Proof
	InfS pr.InfStrength
	ModS pr.ModStrength
	Met  bool // Whether the goal of the proof was met.
}

func (drv *Derivation) deriveAtStrength() (met bool) {
	var (
		lis []*pr.LineInfo
		tot int
	)

	lis, _ = drv.Prf.GetLocalLines()

	tot = 1 + drv.pushAssumptions(lis[0].WffG, drv.Prf)

	// fmt.Printf("DEBUG: Check proof skeleton for incorrectness:\n%s\n", drv.Prf.ConvertToFitchString())

	if _, drv.Met = drv.Prf.IsWffGMet(); !drv.Met {
		for tot != 0 && !drv.Met {
			if tot = pushRules(drv); tot == 0 {
				tot += drv.helpEliminations() + drv.helpDistributions()
			}

			_, drv.Met = drv.Prf.IsWffGMet()
		}
	}

	met = drv.Met

	// fmt.Printf("DEBUG: Check for failure or other oddities:\n%s\n", drv.Prf.ConvertToFitchString())

	return
}
