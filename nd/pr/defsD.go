package pr

import "Deriver/fmla"

type domain struct {
	pcs map[fmla.Predicate]bool // A map as to whether a predicate is present in the proof.
	acs map[fmla.Argument]bool  // A map as to whether an argument is present in the proof.
}

func newDomain() (dom *domain) {
	var (
		pc fmla.Predicate
		ac fmla.Argument
	)

	dom = &domain{
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

func updateDomain(dom *domain, wff *fmla.WffTree) (domU *domain) {
	var (
		pcs []fmla.Predicate
		acs []fmla.Argument
		pc  fmla.Predicate
		ac  fmla.Argument
	)

	// Deeply copy domA to domB.
	domU = newDomain()

	for pc = range dom.pcs {
		domU.pcs[pc] = dom.pcs[pc]
	}

	for ac = range dom.acs {
		domU.acs[ac] = dom.acs[ac]
	}

	// Update domB with the new constants in wff.
	pcs, acs = fmla.GetConstants(wff)

	for _, pc = range pcs {
		domU.pcs[pc] = true
	}

	for _, ac = range acs {
		domU.acs[ac] = true
	}

	return
}

func findArbConsts(dom *domain, wff *fmla.WffTree) (apc fmla.Predicate, aac fmla.Argument) {
	var (
		pcs []fmla.Predicate
		acs []fmla.Argument
		pc  fmla.Predicate
		ac  fmla.Argument
	)

	pcs, acs = fmla.GetConstants(wff)

	for _, pc = range pcs {
		if !dom.pcs[pc] {
			apc = pc

			break
		}
	}

	for _, ac = range acs {
		if !dom.acs[ac] {
			aac = ac

			break
		}
	}

	return
}
