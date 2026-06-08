package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
	"fmt"
	"slices"
)

type Deriver struct {
	Prf  *pr.Proof
	SynB pr.SynBreadth
	InfS pr.InfStrength
	ModS pr.ModStrength
	Met  bool // Whether the goal of the base proof was met.
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
		tot = 1

		for 0 < tot && !drv.Met {
			tot = pushRules(drv)

			_, drv.Met = drv.Prf.HasWffInLines(wffG)

			// if lenP := drv.Prf.CountAllOpenLines(); 100 < lenP && drv.ModS != pr.NoModality {
			// 	fmt.Printf("DEBUG: This proof is way too long:\n%s\n", drv.Prf.ConvertToFitchString())
			// 	panic("Overlong proof.")
			// }
		}
	}

	met = drv.Met

	// fmt.Printf("DEBUG: Check for failure or other oddities:\n%s\n", drv.Prf.ConvertToFitchString())

	return
}

type drvSys struct {
	infS pr.InfStrength
	modS pr.ModStrength
}

func pumpDeriversAtStrengths(wffG *fmla.Wff, wffsP ...*fmla.Wff) (drvs []*Deriver) {
	var (
		drv        *Deriver
		seen       map[drvSys]bool
		mods       []pr.ModStrength
		dexD, lenD int
		mod        pr.ModStrength
		sys        drvSys
	)

	drv = NewDeriver(pr.Implicational, pr.NoModality, wffG, wffsP...)

	drvs = append(drvs, drv)

	seen = map[drvSys]bool{
		{drv.InfS, drv.ModS}: true,
	}

	mods = []pr.ModStrength{pr.ModalK, pr.ModalD, pr.ModalM, pr.Modal4, pr.ModalB}

	dexD, lenD = 0, len(drvs)

	for dexD < lenD {
		if pr.Implicational < drvs[dexD].InfS && drvs[dexD].SynB%pr.ML == 0 {
			for _, mod = range mods {
				if drvs[dexD].ModS%mod != 0 {
					sys = drvSys{drvs[dexD].InfS, drvs[dexD].ModS * mod}

					if !seen[sys] {

						seen[sys] = true

						drv = NewDeriver(sys.infS, sys.modS, wffG, wffsP...)

						drvs = append(drvs, drv)
					}
				}
			}
		}

		if drvs[dexD].InfS < pr.Classical {
			sys = drvSys{drvs[dexD].InfS + 1, drvs[dexD].ModS}

			if !seen[sys] {
				seen[sys] = true

				drv = NewDeriver(sys.infS, sys.modS, wffG, wffsP...)

				drvs = append(drvs, drv)
			}
		}

		// Re-evaluate length after potential appends
		dexD, lenD = dexD+1, len(drvs)
	}

	return
}

func DeriveAtWeakestStrengths(wffG *fmla.Wff, wffsP ...*fmla.Wff) (drvs []*Deriver) {
	var (
		dexD, dexA, lenD int
	)

	// fmt.Printf(
	// 	"DEBUG: The basal strengths are (%d, %d) with this setup:\n%s\n",
	// 	drv.InfS,
	// 	drv.ModS,
	// 	drv.Prf.ConvertToFitchString(),
	// )

	drvs = pumpDeriversAtStrengths(wffG, wffsP...)

	dexD, lenD = 0, len(drvs)

	for dexD < lenD {
		// fmt.Printf(
		// 	"DEBUG: Trying proof of %q at infS %d and modS %d (%s) at index %d.\n",
		// 	fmla.GetWffString(wffG),
		// 	drvs[dexD].InfS,
		// 	drvs[dexD].ModS,
		// 	pr.NameLogic(drvs[dexD].InfS, drvs[dexD].SynB, drvs[dexD].ModS),
		// 	dexD,
		// )

		if drvs[dexD].DeriveAtStrength() {

			for dexA = lenD - 1; dexD < dexA; dexA -= 1 {
				switch {
				case drvs[dexD].InfS < drvs[dexA].InfS:
					drvs = slices.Delete(drvs, dexA, dexA+1)
				case pr.CountModalities(drvs[dexD].ModS) < pr.CountModalities(drvs[dexA].ModS):
					drvs = slices.Delete(drvs, dexA, dexA+1)
				}
			}

			fmt.Printf("DEBUG: Went from %d to %d proofs after succeeding at index %d.\n", lenD, len(drvs), dexD)

			dexD, lenD = dexD+1, len(drvs)
		} else {
			drvs = slices.Delete(drvs, dexD, dexD+1)

			fmt.Printf("DEBUG: Cut down %d to %d proofs after failing at index %d.\n", lenD, len(drvs), dexD)

			lenD -= 1
		}
	}

	return
}
