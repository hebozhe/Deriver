package nd

import "Deriver/fmla"

type Domain struct {
	pcs map[fmla.Predicate]bool
	acs map[fmla.Argument]bool
}

func newDomain(steps ...*Step) (dom *Domain) {
	var (
		step *Step
		pc   fmla.Predicate
		ac   fmla.Argument
		pcs  []fmla.Predicate
		acs  []fmla.Argument
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

	for _, step = range steps {
		pcs, acs = fmla.GetConstants(step.wff)

		for _, pc = range pcs {
			dom.pcs[pc] = true
		}

		for _, ac = range acs {
			dom.acs[ac] = true
		}
	}

	return
}

func getDomain(prf *Proof) (dom *Domain) {
	dom = prf.dom

	return
}

func extendDomain(domA *Domain, steps ...*Step) (domB *Domain) {
	var (
		step *Step
		pcs  []fmla.Predicate
		acs  []fmla.Argument
		pc   fmla.Predicate
		ac   fmla.Argument
	)

	for _, step = range steps {
		pcs, acs = fmla.GetConstants(step.wff)

		for _, pc = range pcs {
			domA.pcs[pc] = true
		}

		for _, ac = range acs {
			domA.acs[ac] = true
		}
	}

	domB = domA

	return
}

func GetConstsFromProofDom(prf *Proof) (pcs []fmla.Predicate, acs []fmla.Argument) {
	var (
		pc fmla.Predicate
		ac fmla.Argument
	)

	if prf == nil {
		panic("Cannot get constants from a nil proof.")
	}

	if prf.dom == nil {
		panic("Cannot get constants from a nil domain.")
	}

	for pc = range prf.dom.pcs {
		if prf.dom.pcs[pc] {
			pcs = append(pcs, pc)
		}
	}

	for ac = range prf.dom.acs {
		if prf.dom.acs[ac] {
			acs = append(acs, ac)
		}
	}

	return
}

func GetArbPred(dom *Domain) (pc fmla.Predicate) {
	if dom == nil {
		panic("Nil domain.")
	}

	for pc = range dom.pcs {
		if !dom.pcs[pc] {

			dom.pcs[pc] = true

			break
		}
	}

	return
}

func GetArbArg(dom *Domain) (ac fmla.Argument) {
	if dom == nil {
		panic("Nil domain.")
	}

	for ac = range dom.acs {
		if !dom.acs[ac] {
			break
		}
	}

	return
}
