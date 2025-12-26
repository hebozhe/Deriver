package pr

import "Deriver/fmla"

type Domain struct {
	pcs map[fmla.Predicate]bool // A map as to whether a predicate is present in the proof.
	acs map[fmla.Argument]bool  // A map as to whether an argument is present in the proof.
}

func newDomain() (dom *Domain) {
	var (
		pc fmla.Predicate
		ac fmla.Argument
	)

	dom = &Domain{
		pcs: map[fmla.Predicate]bool{},
		acs: map[fmla.Argument]bool{},
	}

	for _, pc = range fmla.PredConsts {
		dom.pcs[pc] = false
	}

	for _, ac = range fmla.ArgConsts {
		dom.acs[ac] = false
	}

	return
}

func updateDomain(domA *Domain, wff *fmla.WffTree) (domB *Domain) {
	var (
		pcs []fmla.Predicate
		acs []fmla.Argument
		pc  fmla.Predicate
		ac  fmla.Argument
	)

	// Deeply copy domA to domB.
	domB = newDomain()

	for pc = range domA.pcs {
		domB.pcs[pc] = domA.pcs[pc]
	}

	for ac = range domA.acs {
		domB.acs[ac] = domA.acs[ac]
	}

	// Update domB with the new constants in wff.
	pcs, acs = fmla.GetConstants(wff)

	for _, pc = range pcs {
		domB.pcs[pc] = true
	}

	for _, ac = range acs {
		domB.acs[ac] = true
	}

	return
}

func findArbConsts(dom *Domain, subdom *Domain) (apc fmla.Predicate, aac fmla.Argument) {
	var (
		pc  fmla.Predicate
		ac  fmla.Argument
		has bool
	)

	for pc, has = range dom.pcs {
		if has && !subdom.pcs[pc] {
			apc = pc

			break
		}
	}

	for ac, has = range dom.acs {
		if has && !subdom.acs[ac] {
			aac = ac

			break
		}
	}

	return
}

func GetArbitraryConst(prf *Proof) (apc fmla.Predicate, aac fmla.Argument) {
	var (
		pc fmla.Predicate
		ac fmla.Argument
	)

	for _, pc = range fmla.PredConsts {
		if !prf.dom.pcs[pc] {
			apc = pc

			break
		}
	}

	for _, ac = range fmla.ArgConsts {
		if !prf.dom.acs[ac] {
			aac = ac

			break
		}
	}

	return
}
