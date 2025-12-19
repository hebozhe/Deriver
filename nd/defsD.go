package nd

import "Deriver/fmla"

type Domain struct {
	PCsIn  map[fmla.Predicate]struct{} // What predicate constants are in the domain?
	PCsOut map[fmla.Predicate]struct{} // What predicate constants are out of the domain?
	ACsIn  map[fmla.Argument]struct{}  // What argument constants are in the domain?
	ACsOut map[fmla.Argument]struct{}  // What argument constants are out of the domain?
}

func GetDomain(prf *Proof) (dom *Domain) {
	var (
		step *Step
		pcs  []fmla.Predicate
		acs  []fmla.Argument
		pc   fmla.Predicate
		ac   fmla.Argument
		ok   bool
	)

	dom = &Domain{
		PCsIn:  map[fmla.Predicate]struct{}{},
		PCsOut: map[fmla.Predicate]struct{}{},
		ACsIn:  map[fmla.Argument]struct{}{},
		ACsOut: map[fmla.Argument]struct{}{},
	}

	for _, step = range prf.Steps {
		pcs, acs = fmla.GetConstants(step.Wff)

		for _, pc = range pcs {
			dom.PCsIn[pc] = struct{}{}
		}

		for _, ac = range acs {
			dom.ACsIn[ac] = struct{}{}
		}

	}

	for _, pc = range fmla.PredConsts {
		if _, ok = dom.PCsIn[pc]; !ok {
			dom.PCsOut[pc] = struct{}{}
		}
	}

	for _, ac = range fmla.ArgConsts {
		if _, ok = dom.ACsIn[ac]; !ok {
			dom.ACsOut[ac] = struct{}{}
		}
	}

	return
}

func MovePCIntoDom(prf *Proof) (dom *Domain, pc fmla.Predicate) {
	var (
		opc fmla.Predicate
	)

	dom = prf.Dom

	for opc = range dom.PCsOut {
		pc = opc

		break
	}

	delete(dom.PCsOut, pc)

	dom.PCsIn[pc] = struct{}{}

	return
}

func MovePCOutOfDom(prf *Proof) (dom *Domain, pc fmla.Predicate) {
	var (
		ipc fmla.Predicate
	)

	dom = prf.Dom

	for ipc = range dom.PCsIn {
		pc = ipc

		break
	}

	delete(dom.PCsIn, pc)

	dom.PCsOut[pc] = struct{}{}

	return
}

func MoveACIntoDom(prf *Proof) (dom *Domain, ac fmla.Argument) {
	var (
		oac fmla.Argument
	)

	dom = prf.Dom

	for oac = range dom.ACsOut {
		ac = oac

		break
	}

	delete(dom.ACsOut, ac)

	dom.ACsIn[ac] = struct{}{}

	return
}

func MoveACOutOfDom(prf *Proof) (dom *Domain, ac fmla.Argument) {
	var (
		iac fmla.Argument
	)

	dom = prf.Dom

	for iac = range dom.ACsIn {
		ac = iac

		break
	}

	delete(dom.ACsIn, ac)

	dom.ACsOut[ac] = struct{}{}

	return
}
