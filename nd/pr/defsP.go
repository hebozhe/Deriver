package pr

import (
	"Deriver/fmla"
	"Deriver/gen"
	"iter"
	"slices"
)

type Line struct {
	wff        *fmla.Wff // The wff at the line.
	rule       NDRule    // The rule used to derive the line.
	j1, j2, j3 *Line     // Justifications of the line.

	prf *Prf // The proof where the line is located.
}

func (ln *Line) Wff() (wff *fmla.Wff) {
	wff = ln.wff.DeepCopy()

	return
}

func (ln *Line) Rule() (rule NDRule) {
	rule = ln.rule

	return
}

func (ln *Line) Justs() (j1, j2, j3 *Line, numJ int) {
	if ln.j1 != nil {
		j1, numJ = ln.j1, numJ+1
	}

	if ln.j2 != nil {
		j2, numJ = ln.j2, numJ+1
	}

	if ln.j3 != nil {
		j3, numJ = ln.j3, numJ+1
	}

	return
}

func (ln *Line) Prf() (prf *Prf) {
	prf = ln.prf

	return
}

func (ln *Line) TraceJusts(withP bool) (traceJ map[*Line]bool, traceP map[*Prf]bool) {
	var (
		stackJ []*Line
		lenS   int
		lnJ    *Line
	)

	traceJ = map[*Line]bool{ln: true}

	stackJ, lenS = []*Line{ln}, 1

	for 0 < lenS {
		lnJ, stackJ = stackJ[lenS-1], stackJ[:lenS-1]

		if lnJ.j3 != nil && !traceJ[lnJ.j3] {
			traceJ[lnJ.j3], stackJ, lenS = true, append(stackJ, lnJ.j3), lenS+1
		}

		if lnJ.j2 != nil && !traceJ[lnJ.j2] {
			traceJ[lnJ.j2], stackJ, lenS = true, append(stackJ, lnJ.j2), lenS+1
		}

		if lnJ.j1 != nil && !traceJ[lnJ.j1] {
			traceJ[lnJ.j1], stackJ, lenS = true, append(stackJ, lnJ.j1), lenS+1
		}

		lenS = len(stackJ)
	}

	if withP {
		traceP = map[*Prf]bool{}

		for lnJ = range traceJ {
			traceP[lnJ.prf] = true
		}
	}

	return
}

type Prf struct {
	wffG *fmla.Wff // The proof's goal WFF, which is local to the proof.
	wffD *fmla.Wff // The proof's output WFF upon a proof's discharge, which can differ from the local goal.

	depthP int // The depth of the proof.
	depthM int // The modal depth of the proof.

	purp NDRule // The proof's purpose (the rule that will discharge the proof).

	open bool // Whether the proof remains open.

	lns []*Line

	prfO  *Prf   // The superproof to this proof, which is nil if it's the base proof.
	prfsI []*Prf // The subproofs to this proof.

	// These are cached constants that hold in a fixed proof state where the number of lines does not increase:
	freshPC fmla.Predicate   // A predicate constant that is **not** used in the proof or its outer proofs at the same modal depth.
	freshAC fmla.Argument    // An argument constant that is **not** used in the proof or its outer proofs at the same modal depth.
	usedPCs []fmla.Predicate // The predicates used in the proof.
	usedACs []fmla.Argument  // The arguments used in the proof.
}

func (prf *Prf) WffG() (wffG *fmla.Wff) {
	wffG = prf.wffG.DeepCopy()

	return
}

func (prf *Prf) WffD() (disG *fmla.Wff) {
	disG = prf.wffD.DeepCopy()

	return
}

func (prf *Prf) DepthP() (depthP int) {
	depthP = prf.depthP

	return
}

func (prf *Prf) DepthM() (depthM int) {
	depthM = prf.depthM

	return
}

func (prf *Prf) Purp() (purp NDRule) {
	purp = prf.purp

	return
}

func (prf *Prf) IsOpen() (is bool) {
	is = prf.open

	return
}

func (prf *Prf) Lines() (lns iter.Seq[*Line]) {
	lns = func(yield func(*Line) bool) {
		var (
			dex, lenS int
		)

		for dex, lenS = 0, len(prf.lns); dex < lenS; dex += 1 {
			if !yield(prf.lns[dex]) {
				break
			}

			// Check the proof's line length dynamically.
			lenS = len(prf.lns)
		}
	}

	return
}

func (prf *Prf) LineAtIndex(dex int) (ln *Line) {
	var (
		lenL int
	)

	if -1 < dex {
		if lenL = len(prf.lns); dex < lenL {
			ln = prf.lns[dex]
		}
	}

	return
}

func (prf *Prf) LineWithWff(wff *fmla.Wff) (ln *Line) {
	var dex int

	dex = slices.IndexFunc(prf.lns, func(lnN *Line) (has bool) {
		has = lnN.wff.Is(wff)

		return
	})

	if -1 < dex {
		ln = prf.lns[dex]
	}

	return
}

func (prf *Prf) PrfO() (prfO *Prf) {
	prfO = prf.prfO

	return
}

func (prf *Prf) Root(depthM int) (root *Prf) {
	for root = prf; root.prfO != nil; root = root.prfO {
		if root.prfO != nil && root.prfO.depthM < depthM {
			break
		}

		if depthM < root.depthM {
			panic("No root is available at the provided modal depth.")
		}
	}

	return
}

func (prf *Prf) PrfsI() (prfsI iter.Seq[*Prf]) {
	prfsI = func(yield func(*Prf) bool) {
		var (
			dex, lenP int
		)

		for dex, lenP = 0, len(prf.prfsI); dex < lenP; dex += 1 {
			if !yield(prf.prfsI[dex]) {
				break
			}

			// Check the proof's subproof length dynamically.
			lenP = len(prf.prfsI)
		}
	}

	return
}

func allLeaves(prf *Prf) (prfsI []*Prf) {
	var (
		lenI int
		prfI *Prf
	)

	if lenI = len(prf.prfsI); lenI == 0 {
		prfsI = []*Prf{prf}
	} else {
		for _, prfI = range prf.prfsI {
			prfsI = append(prfsI, allLeaves(prfI)...)
		}
	}

	return
}

func descendToDepthM(prfsI []*Prf, depthM int) (prfs []*Prf) {
	var (
		prfI *Prf
	)

	for _, prfI = range prfsI {
		if prfI.depthM == depthM {
			prfs = append(prfs, prfI)
		} else if depthM < prfI.depthM && prfI.prfO != nil {
			prfs = append(prfs, prfI.prfO)
		}
	}

	if !slices.Equal(prfsI, prfs) {
		prfs = descendToDepthM(prfs, depthM)
	}

	return
}

func (prf *Prf) Leaves(depthM int, open bool) (leaves iter.Seq[*Prf]) {
	var (
		prfsI []*Prf
	)

	prfsI = allLeaves(prf)
	prfsI = descendToDepthM(prfsI, depthM)

	if open {
		prfsI = slices.DeleteFunc(prfsI, func(prfI *Prf) (nix bool) { nix = !prfI.open; return })
	}

	leaves = func(yield func(*Prf) bool) {
		var (
			prfI *Prf
		)

		for _, prfI = range prfsI {
			if !yield(prfI) {
				break
			}
		}
	}

	return
}

func (prf *Prf) DistP(prfI *Prf) (distP int) {
	var (
		prfO *Prf
	)

	if prf == prfI {
		distP = 0
	} else {
		distP = -1

		for prfO = prfI.prfO; prfO != nil; prfO = prfO.prfO {
			if prfO == prf {
				distP = prfI.depthP - prf.depthP

				break
			}
		}
	}

	return
}

func (prf *Prf) DistM(prfI *Prf) (distM int) {
	var (
		prfO *Prf
	)

	if prf == prfI {
		distM = 0
	} else {
		distM = -1

		for prfO = prfI.prfO; prfO != nil; prfO = prfO.prfO {
			if prfO == prf {
				distM = prfI.depthM - prf.depthM

				break
			}
		}
	}

	return
}

func (prf *Prf) UsedPCs() (upcs []fmla.Predicate) {
	var (
		pcs []fmla.Predicate
		ln  *Line
	)

	if upcs = prf.usedPCs; upcs == nil {
		pcs, _ = prf.wffG.AllConsts(false)

		upcs = append(upcs, pcs...)

		for ln = range prf.Lines() {
			pcs, _ = ln.wff.AllConsts(false)

			upcs = append(upcs, pcs...)
		}

		if prf.prfO != nil && prf.prfO.depthM == prf.depthM {
			pcs = prf.prfO.UsedPCs()

			upcs = append(upcs, pcs...)
		}

		upcs = gen.TupSet(upcs)
		upcs = gen.TupDifference(upcs, fmla.SpecPredConsts)

		prf.usedPCs = append([]fmla.Predicate{}, upcs...)
	} else {
		upcs = append([]fmla.Predicate{}, upcs...)
	}

	return
}

func (prf *Prf) UsedACs() (uacs []fmla.Argument) {
	var (
		acs []fmla.Argument
		ln  *Line
	)

	if uacs = prf.usedACs; uacs == nil {
		_, acs = prf.wffG.AllConsts(false)

		uacs = append(uacs, acs...)

		for ln = range prf.Lines() {
			_, acs = ln.wff.AllConsts(false)

			uacs = append(uacs, acs...)
		}

		if prf.prfO != nil && prf.prfO.depthM == prf.depthM {
			acs = prf.prfO.UsedACs()

			uacs = append(uacs, acs...)
		}

		uacs = gen.TupSet(uacs)

		prf.usedACs = append([]fmla.Argument{}, uacs...)
	} else {
		uacs = append([]fmla.Argument{}, uacs...)
	}

	return
}

func (prf *Prf) FreshPC() (fpc fmla.Predicate) {
	var (
		allPCs  []fmla.Predicate
		usedPCs []fmla.Predicate
		ln      *Line
		pcs     []fmla.Predicate
		prfO    *Prf
	)

	if fpc = prf.freshPC; fpc == fmla.NoPred {
		allPCs = gen.TupDifference(fmla.PredConsts, fmla.SpecPredConsts)

		pcs, _ = prf.wffG.AllConsts(false)

		usedPCs = append(usedPCs, pcs...)

		for ln = range prf.Lines() {
			pcs, _ = ln.wff.AllConsts(false)

			usedPCs = append(usedPCs, pcs...)
		}

		for prfO = prf.prfO; prfO != nil; prfO = prfO.prfO {
			if prfO.depthM != prf.depthM {
				break
			}

			pcs, _ = prfO.wffG.AllConsts(false)

			usedPCs = append(usedPCs, pcs...)

			for ln = range prfO.Lines() {
				pcs, _ = ln.wff.AllConsts(false)

				usedPCs = append(usedPCs, pcs...)
			}
		}

		allPCs = gen.TupDifference(allPCs, usedPCs)

		for _, fpc = range allPCs {
			prf.freshPC = fpc

			break
		}
	}

	return
}

func (prf *Prf) FreshAC() (fac fmla.Argument) {
	var (
		allACs  []fmla.Argument
		usedACs []fmla.Argument
		ln      *Line
		acs     []fmla.Argument
		prfO    *Prf
	)

	if fac = prf.freshAC; fac == fmla.NoArg {
		allACs = append(allACs, fmla.ArgConsts...)

		_, acs = prf.wffG.AllConsts(false)

		usedACs = append(usedACs, acs...)

		for ln = range prf.Lines() {
			_, acs = ln.wff.AllConsts(false)

			usedACs = append(usedACs, acs...)
		}

		for prfO = prf.prfO; prfO != nil; prfO = prfO.prfO {
			if prfO.depthM != prf.depthM {
				break
			}

			_, acs = prfO.wffG.AllConsts(false)

			usedACs = append(usedACs, acs...)

			for ln = range prfO.Lines() {
				_, acs = ln.wff.AllConsts(false)

				usedACs = append(usedACs, acs...)
			}
		}

		allACs = gen.TupDifference(allACs, usedACs)

		for _, fac = range allACs {
			prf.freshAC = fac

			break
		}
	}

	return
}

func (prf *Prf) HasPrf(prfI *Prf, depthM int) (has bool) {
	var (
		prfO *Prf
	)

	has = slices.ContainsFunc(prf.prfsI, func(prfN *Prf) (con bool) {
		con = prfN.purp == prfI.purp && prfN.depthM == depthM &&
			prfN.lns[0].wff.Is(prfI.lns[0].wff) && prfN.wffD.Is(prfI.wffD)

		return
	})

	has = has ||
		(prf.purp == prfI.purp && prf.depthM == depthM && prf.lns[0].wff.Is(prfI.lns[0].wff) && prf.wffD.Is(prfI.wffD))

	for prfO = prf.prfO; prfO != nil && !has; prfO = prfO.prfO {
		if prfO.depthM < depthM {
			break
		}

		has = prfO.purp == prfI.purp && prfO.depthM == depthM &&
			prfO.lns[0].wff.Is(prfI.lns[0].wff) && prfO.wffD.Is(prfI.wffD)
	}

	return
}

func (prf *Prf) HasLine(ln *Line) (has bool) {
	has = slices.ContainsFunc(prf.lns, func(lnN *Line) (con bool) {
		con = lnN.wff.Is(ln.wff)

		return
	})

	if !has && ln.rule != Reit {
		has = prf.prfO != nil && prf.prfO.depthM == prf.depthM && prf.prfO.HasLine(ln)
	}

	return
}

func InnermostProof(prfs ...*Prf) (prf *Prf) {
	var (
		lenP       int
		prfA, prfB *Prf
	)

	switch lenP = len(prfs); lenP {
	case 0:
		prf = nil
	case 1:
		prf = prfs[0]
	default:
		if prfA = prfs[0]; prfA == nil {
			prf = nil
		} else if prfB = InnermostProof(prfs[1:]...); prfB == nil {
			prf = nil
		} else {
			switch {
			case prfA == prfB, -1 < prfA.DistP(prfB):
				prf = prfB
			case -1 < prfB.DistP(prfA):
				prf = prfA
			}
		}
	}

	return
}
