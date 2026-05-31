package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
)

type Deriver struct {
	Prf  *pr.Proof
	SynB pr.SynBreadth
	InfS pr.InfStrength
	ModS pr.ModStrength
	Met  bool // Whether the goal of the proof was met.
}

func NewDeriver(infS pr.InfStrength, modS pr.ModStrength, wffG *fmla.Wff, wffsP ...*fmla.Wff) (drv *Deriver) {
	var (
		prf  *pr.Proof
		synB pr.SynBreadth
	)

	prf, synB = pr.NewProof(wffG, wffsP...)

	drv = &Deriver{
		Prf:  prf,
		SynB: synB,
		InfS: infS,
		ModS: modS,
		Met:  false,
	}

	return
}

func (drv *Deriver) DeriveAtStrength() (met bool) {
	var (
		tot  int
		wffG *fmla.Wff
	)

	wffG = drv.Prf.GetWffG()

	tot = drv.pushAssumptions(wffG, drv.Prf) + 1

	// fmt.Printf("DEBUG: Check proof skeleton for incorrectness:\n%s\n", drv.Prf.ConvertToFitchString())

	if _, drv.Met = drv.Prf.HasWffInLines(wffG); !drv.Met {
		for 0 < tot && !drv.Met {
			tot = pushRules(drv)

			_, drv.Met = drv.Prf.HasWffInLines(wffG)

			// if lenP := drv.Prf.CountAllOpenLines(); 1000 < lenP {
			// 	fmt.Printf("DEBUG: This proof is way too long:\n%s\n", drv.Prf.ConvertToFitchString())
			// 	panic("Overlong proof.")
			// }
		}
	}

	met = drv.Met

	// fmt.Printf("DEBUG: Check for failure or other oddities:\n%s\n", drv.Prf.ConvertToFitchString())

	return
}
