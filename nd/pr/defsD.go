package pr

import (
	"Deriver/fmla"
)

type Domain struct {
	pcs map[fmla.Predicate]bool
	acs map[fmla.Argument]bool
	pvs map[fmla.Predicate]bool
	avs map[fmla.Argument]bool

	apc fmla.Predicate
	aac fmla.Argument
}

func newDomain() (dom *Domain) {
	var (
		pred fmla.Predicate
		arg  fmla.Argument
	)

	dom = &Domain{
		pcs: map[fmla.Predicate]bool{},
		acs: map[fmla.Argument]bool{},
		pvs: map[fmla.Predicate]bool{},
		avs: map[fmla.Argument]bool{},
		apc: 0,
		aac: 0,
	}

	for _, pred = range fmla.PredConsts {
		dom.pcs[pred] = false
	}

	for _, arg = range fmla.ArgConsts {
		dom.acs[arg] = false
	}

	for _, pred = range fmla.PredVars {
		dom.pvs[pred] = false
	}

	for _, arg = range fmla.ArgVars {
		dom.avs[arg] = false
	}

	return
}

func (dom *Domain) updateDomain(wffs ...*fmla.WffTree) (domU *Domain) {
	var (
		pcs, pvs []fmla.Predicate
		acs, avs []fmla.Argument
		pred     fmla.Predicate
		arg      fmla.Argument
		wff      *fmla.WffTree
	)

	domU = newDomain()

	for pred = range dom.pcs {
		domU.pcs[pred] = dom.pcs[pred]
	}

	for arg = range dom.acs {
		domU.acs[arg] = dom.acs[arg]
	}

	for pred = range dom.pvs {
		domU.pvs[pred] = dom.pvs[pred]
	}

	for arg = range dom.avs {
		domU.avs[arg] = dom.avs[arg]
	}

	for _, wff = range wffs {
		pcs, acs = fmla.GetConstants(wff)
		pvs, avs = fmla.GetVariables(wff)

		for _, pred = range pcs {
			domU.pcs[pred] = true
		}

		for _, arg = range acs {
			domU.acs[arg] = true
		}

		for _, pred = range pvs {
			domU.pvs[pred] = true
		}

		for _, arg = range avs {
			domU.avs[arg] = true
		}
	}

	return
}

func (dom *Domain) findUniqueConstants(domO *Domain, wffs ...*fmla.WffTree) (apc fmla.Predicate, aac fmla.Argument) {
	var (
		wff *fmla.WffTree
		pcs []fmla.Predicate
		acs []fmla.Argument
		pc  fmla.Predicate
		ac  fmla.Argument
	)

	for _, wff = range wffs {
		pcs, acs = fmla.GetConstants(wff)

		for _, pc = range pcs {
			if !domO.pcs[pc] {
				apc = pc

				break
			}
		}

		for _, ac = range acs {
			if !domO.acs[ac] {
				aac = ac

				break
			}
		}

		if apc != 0 && aac != 0 {
			break
		}
	}

	if apc == 0 && aac == 0 {
		panic("Could not find unique constants.")
	}

	return
}
