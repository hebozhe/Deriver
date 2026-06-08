package pr

import (
	"Deriver/fmla"
	"slices"
)

type Line struct {
	wff        *fmla.Wff
	rule       NDRule
	j1, j2, j3 *Line

	prf *Proof // The proof to which this line belongs.

	ext bool // Whether the line has been extended.
}

func (ln *Line) GetWff() (wff *fmla.Wff) {
	wff = fmla.DeepCopy(ln.wff)

	return
}

func (ln *Line) GetRule() (rule NDRule) {
	rule = ln.rule

	return
}

func (ln *Line) GetProof() (prf *Proof) {
	prf = ln.prf

	return
}

func (ln *Line) GetJustifications() (js []*Line) {
	switch {
	case ln.j3 != nil:
		js = append(js, ln.j1, ln.j2, ln.j3)
	case ln.j2 != nil:
		js = append(js, ln.j1, ln.j2)
	case ln.j1 != nil:
		js = append(js, ln.j1)
	}

	return
}

func (ln *Line) GetJustificationsDependencies() (depsJ map[*Line]bool) {
	var (
		tmpJ map[*Line]bool
		j    *Line
	)

	depsJ = map[*Line]bool{ln: true}

	if ln.j1 != nil {
		tmpJ = ln.j1.GetJustificationsDependencies()

		for j = range tmpJ {
			depsJ[j] = true
		}
	}

	if ln.j2 != nil {
		tmpJ = ln.j2.GetJustificationsDependencies()

		for j = range tmpJ {
			depsJ[j] = true
		}
	}

	if ln.j3 != nil {
		tmpJ = ln.j3.GetJustificationsDependencies()

		for j = range tmpJ {
			depsJ[j] = true
		}
	}

	return
}

func (ln *Line) GetProofDependencies() (depsP map[*Proof]bool) {
	var (
		tmpP map[*Proof]bool
		prf  *Proof
	)

	depsP = map[*Proof]bool{ln.prf: true}

	if ln.j1 != nil {
		tmpP = ln.j1.GetProofDependencies()

		for prf = range tmpP {
			depsP[prf] = true
		}
	}

	if ln.j2 != nil {
		tmpP = ln.j2.GetProofDependencies()

		for prf = range tmpP {
			depsP[prf] = true
		}
	}

	if ln.j3 != nil {
		tmpP = ln.j3.GetProofDependencies()

		for prf = range tmpP {
			depsP[prf] = true
		}
	}

	return
}

func (ln *Line) IsExtended() (is bool) {
	is = ln.ext

	return
}

func (ln *Line) SetExtended(ext bool) (is bool) {
	ln.ext, is = ext, ext

	return
}

type Proof struct {
	wffG *fmla.Wff

	purp NDRule
	open bool

	lns []*Line

	prfO  *Proof
	prfsI []*Proof

	pvG fmla.Predicate // The goal predicate variable in a QL subproof.
	avG fmla.Argument  // The goal argument variable in a QL subproof.
	pcA fmla.Predicate // The fresh predicate variable in QL subproof.
	acA fmla.Argument  // The fresh argument variable in QL subproof.

	fpcs []fmla.Predicate // Fresh predicate constants.
	facs []fmla.Argument  // Fresh argument constants.

	pd int // Proof depth of the proof.
	md int // Modal depth of the proof.
}

func (prf *Proof) GetWffG() (wffG *fmla.Wff) {
	wffG = fmla.DeepCopy(prf.wffG)

	return
}

func (prf *Proof) GetPurp() (purp NDRule) {
	purp = prf.purp

	return
}

func (prf *Proof) IsOpen() (is bool) {
	is = prf.open

	return
}

func (prf *Proof) GetLines() (lns []*Line) {
	lns = append(lns, prf.lns...)

	return
}

func (prf *Proof) GetLineAtIndex(dex int) (ln *Line) {
	var (
		lenL int
	)

	if lenL = len(prf.lns); dex < lenL {
		ln = prf.lns[dex]
	}

	return
}

func (prf *Proof) GetWffAtLineIndex(dex int) (wff *fmla.Wff) {
	var (
		ln *Line
	)

	if ln = prf.GetLineAtIndex(dex); ln != nil {
		wff = ln.GetWff()
	}

	return
}

func (prf *Proof) GetModalDepth() (md int) {
	md = prf.md

	return
}

func (prf *Proof) GetModalDistance(toPrf *Proof) (mD int) {
	if prf == toPrf {
		mD = 0
	} else if prf.IsOuter(toPrf) {
		mD = toPrf.md - prf.md
	} else {
		mD = -1
	}

	return
}

func (prf *Proof) GetInnerProofs(self bool) (prfsI []*Proof) {
	var (
		prfI   *Proof
		dex    int
		prfsII []*Proof
	)

	if self {
		prfsI = append(prfsI, prf)
	}

	prfsI = append(prfsI, prf.prfsI...)

	for dex, prfI = range prfsI {
		prfsII = prfI.GetInnerProofs(false)

		prfsI = slices.Insert(prfsI, dex, prfsII...)
	}

	return
}

func (prf *Proof) GetInnerProofsAtModalDistance(self bool, md int) (prfsI []*Proof) {
	var (
		delFunc func(prfI *Proof) (nix bool)
	)

	prfsI = prf.GetInnerProofs(self)

	delFunc = func(prfI *Proof) (nix bool) {
		nix = prf.GetModalDistance(prfI) != md

		return
	}

	prfsI = slices.DeleteFunc(prfsI, delFunc)

	return
}

func (prf *Proof) GetOuterProof() (prfO *Proof) {
	prfO = prf.prfO

	return
}

func (prf *Proof) GetOuterProofsAtModalDistance(self bool, md int) (prfsO []*Proof) {
	var (
		delFunc func(prfO *Proof) (nix bool)
	)

	prfsO = prf.GetOuterProofs(self)

	delFunc = func(prfO *Proof) (nix bool) {
		nix = prfO.GetModalDistance(prf) != md

		return
	}

	prfsO = slices.DeleteFunc(prfsO, delFunc)

	return
}

func (prf *Proof) GetQLInnerProofPredicates() (pcA, pvG fmla.Predicate, ok bool) {
	pcA, pvG = prf.pcA, prf.pvG

	ok = pcA != 0 && pvG != 0

	return
}

func (prf *Proof) GetQLInnerProofArguments() (acA, avG fmla.Argument, ok bool) {
	acA, avG = prf.acA, prf.avG

	ok = acA != 0 && avG != 0

	return
}

func (prf *Proof) SetQLInnerProofPredicates(pcA, pvG fmla.Predicate) (ok bool) {
	if ok = slices.Contains(fmla.PredConsts, pcA) && slices.Contains(fmla.PredVars, pvG); ok {
		prf.pcA, prf.pvG = pcA, pvG
	}

	return
}

func (prf *Proof) SetQLInnerProofArguments(acA, avG fmla.Argument) (ok bool) {
	if ok = slices.Contains(fmla.ArgConsts, acA) && slices.Contains(fmla.ArgVars, avG); ok {
		prf.acA, prf.avG = acA, avG
	}

	return
}

func reduceFreshConstants(prf *Proof, wffs ...*fmla.Wff) (fpcs []fmla.Predicate, facs []fmla.Argument) {
	var (
		wff *fmla.Wff
		pcs []fmla.Predicate
		acs []fmla.Argument
		pc  fmla.Predicate
		ac  fmla.Argument
		dex int
	)

	fpcs, facs = append(fpcs, prf.fpcs...), append(facs, prf.facs...)

	for _, wff = range wffs {
		pcs, acs = fmla.GetConstants(wff)

		for _, pc = range pcs {
			if dex = slices.Index(fpcs, pc); -1 < dex {
				fpcs = slices.Delete(fpcs, dex, dex+1)
			}
		}

		for _, ac = range acs {
			if dex = slices.Index(facs, ac); -1 < dex {
				facs = slices.Delete(facs, dex, dex+1)
			}
		}
	}

	return
}

func (prf *Proof) GetOuterProofs(self bool) (prfsO []*Proof) {
	var (
		prfO *Proof
	)

	prfO = prf.prfO

	for prfO != nil {
		prfsO = append(prfsO, prfO)

		prfO = prfO.prfO
	}

	slices.Reverse(prfsO) // Sort from outer to inner.

	if self {
		prfsO = append(prfsO, prf) // The proof, itself, is the innermost.
	}

	return
}

func (prf *Proof) GetFreshPredicate() (pc fmla.Predicate, ok bool) {
	var (
		lenC int
	)

	if lenC = len(prf.fpcs); 0 < lenC {
		pc, ok = prf.fpcs[0], true
	}

	return
}

func (prf *Proof) GetFreshArgument() (ac fmla.Argument, ok bool) {
	var (
		lenC int
	)

	if lenC = len(prf.facs); 0 < lenC {
		ac, ok = prf.facs[0], true
	}

	return
}

func (prf *Proof) GetUsedPredicates() (pcs []fmla.Predicate) {
	var (
		pc  fmla.Predicate
		dex int
	)

	pcs = append(pcs, fmla.PredConsts...)

	for _, pc = range prf.fpcs {
		if dex = slices.Index(pcs, pc); -1 < dex {
			pcs = slices.Delete(pcs, dex, dex+1)
		}
	}

	return
}

func (prf *Proof) GetUsedArguments() (acs []fmla.Argument) {
	var (
		fac fmla.Argument
		dex int
	)

	acs = append(acs, fmla.ArgConsts...)

	for _, fac = range prf.facs {
		if dex = slices.Index(acs, fac); -1 < dex {
			acs = slices.Delete(acs, dex, dex+1)
		}
	}

	return
}

func (prf *Proof) GetAllProofs() (prfs []*Proof) {
	var (
		prfsI []*Proof
	)

	prfs = prf.GetOuterProofs(true)

	prfsI = prf.GetInnerProofs(false)

	prfs = append(prfs, prfsI...)

	return
}

func (prf *Proof) HasWffInLines(wff *fmla.Wff) (lnW *Line, has bool) {
	var (
		ln *Line
	)

	for _, ln = range prf.lns {
		if has = fmla.IsIdentical(ln.wff, wff); has {
			lnW = ln

			break
		}
	}

	return
}

func (prf *Proof) IsOuter(toPrf *Proof) (is bool) {
	switch {
	case prf == toPrf.prfO:
		is = true
	case toPrf.prfO != nil:
		is = prf.IsOuter(toPrf.prfO)
	}

	return
}

func (prf *Proof) IsReachable(byPrf *Proof) (prfO, prfI *Proof, is bool) {
	switch {
	case prf == byPrf:
		prfO, prfI, is = prf, prf, true
	case prf.IsOuter(byPrf):
		prfO, prfI, is = prf, byPrf, true
	case byPrf.IsOuter(prf):
		prfO, prfI, is = byPrf, prf, true
	}

	return
}

func (prf *Proof) GetProofDepth() (pd int) {
	pd = prf.pd

	return
}

func (prf *Proof) GetProofDistance(toPrf *Proof) (pD int) {
	if prf == toPrf {
		pD = 0
	} else if prf.IsOuter(toPrf) {
		pD = toPrf.pd - prf.pd
	} else {
		pD = -1
	}

	return
}

func (prf *Proof) CloseProof() (tot int) {
	var (
		prfI *Proof
		ln   *Line
	)

	if prf.open {
		prf.open = false

		for _, ln = range prf.lns {
			ln.ext = true
		}

		tot = 1
	}

	for _, prfI = range prf.prfsI {
		tot += prfI.CloseProof()
	}

	return
}

func (prf *Proof) CountLines() (tot int) {
	tot = len(prf.lns)

	return
}

func (prf *Proof) CountAllOpenLines() (tot int) {
	var (
		prfs []*Proof
	)

	prfs = prf.GetAllProofs()

	for _, prf = range prfs {
		if prf.open {
			tot += prf.CountLines()
		}
	}

	return
}

func (prf *Proof) MinimizeProofLines() (prfU *Proof) {
	var (
		delLinesFunc func(lnA *Line) (nix bool)
		lnW          *Line
		dex          int
		has          bool
		depsJ        map[*Line]bool
	)

	delLinesFunc = func(lnA *Line) (nix bool) {
		nix = !depsJ[lnA] && lnA.rule != Assumption

		return
	}

	if lnW, has = prf.HasWffInLines(prf.wffG); has {
		depsJ = lnW.GetJustificationsDependencies()

		prf.lns = slices.DeleteFunc(prf.lns, delLinesFunc)
	}

	for dex = range prf.prfsI {
		prf.prfsI[dex] = prf.prfsI[dex].MinimizeProofLines()
	}

	prfU = prf

	return
}

func (prf *Proof) MinimizeInnerProofs() (prfU *Proof) {
	var (
		delRedundantProofFunc func(prfA *Proof) (nix bool)
		lnW                   *Line
		has                   bool
		depsP                 map[*Proof]bool
		dex                   int
	)

	delRedundantProofFunc = func(prfA *Proof) (nix bool) {
		nix = !depsP[prfA]

		return
	}

	if lnW, has = prf.HasWffInLines(prf.wffG); has {
		depsP = lnW.GetProofDependencies()

		prf.prfsI = slices.DeleteFunc(prf.prfsI, delRedundantProofFunc)
	}

	// Recurse into remaining inner proofs.
	for dex = range prf.prfsI {
		prf.prfsI[dex] = prf.prfsI[dex].MinimizeInnerProofs()
	}

	prfU = prf

	return
}

func (prf *Proof) MinimizeProof() (prfU *Proof) {
	prf = prf.MinimizeProofLines()

	prf = prf.MinimizeInnerProofs()

	prfU = prf

	return
}

func (prf *Proof) FlattenProof() (lns []*Line) {
	var (
		prfI      *Proof
		lnsI      []*Line
		lenI, dex int
		ln        *Line
	)

	lns = prf.GetLines()

FLATTENPROOF_OUTER:
	for _, prfI = range prf.prfsI {
		lnsI = prfI.FlattenProof()

		if lenI = len(lnsI); lenI == 0 {
			continue
		}

		for dex, ln = range lns {
			if !IsDischargeRule(ln.rule) {
				continue
			}

			switch {
			case ln.j3 != nil: // ExistsElim or DiamondElim.
				if lnsI[0] == ln.j2 {
					lns = slices.Insert(lns, dex, lnsI...)

					continue FLATTENPROOF_OUTER
				}
			case ln.j2 != nil: // ToIntro, NegIntro, ForAllIntro, or BoxIntro.
				if lnsI[0] == ln.j1 {
					lns = slices.Insert(lns, dex, lnsI...)

					continue FLATTENPROOF_OUTER
				}
			}
		}

		// Append the lnsI to the end of lns if they're not set elsewhere.
		lns = append(lns, lnsI...)
	}

	return
}

func (prf *Proof) NewLine(wff *fmla.Wff, rule, purp NDRule, js ...*Line) (ln *Line) {
	var (
		lenJ int
	)

	if purp == 0 {
		purp = prf.purp
	}

	if lenJ = len(js); !isJCountCorrect(rule, purp, lenJ) {
		panic("Incorrect number of justification lines.")
	}

	ln = &Line{
		wff:  wff,
		rule: rule,
		// The justifications are worked out below:
		j1: nil,
		j2: nil,
		j3: nil,
		// The proof to which the line belongs is decided after it's inserted.
		prf: prf,
		ext: false,
	}

	switch lenJ {
	case 3:
		ln.j1, ln.j2, ln.j3 = js[0], js[1], js[2]
	case 2:
		ln.j1, ln.j2 = js[0], js[1]
	case 1:
		ln.j1 = js[0]
	}

	return
}

func (prf *Proof) WffIsRedundant(wff *fmla.Wff) (is bool) {
	var (
		prfsO []*Proof
		prfO  *Proof
	)

	prfsO = prf.GetOuterProofsAtModalDistance(true, 0)

	for _, prfO = range prfsO {
		if _, is = prfO.HasWffInLines(wff); is {
			break
		}
	}

	return
}

func (prf *Proof) LineIsRedundant(ln *Line) (is bool) {
	switch ln.rule {
	case Reiteration:
		is = slices.ContainsFunc(prf.lns, func(lnA *Line) (has bool) {
			has = fmla.IsIdentical(lnA.wff, ln.wff) && lnA.rule == ln.rule

			return
		})
	default:
		is = slices.ContainsFunc(prf.lns, func(lnA *Line) (has bool) {
			has = fmla.IsIdentical(lnA.wff, ln.wff)

			return
		})
	}

	if !is && prf.prfO != nil && prf.prfO.GetModalDistance(prf) == 0 {
		is = prf.prfO.LineIsRedundant(ln)
	}

	return
}

func (prf *Proof) InsertLines(lns ...*Line) (tot int) {
	var (
		ln *Line
	)

	for _, ln = range lns {
		if ln == nil || prf.LineIsRedundant(ln) || fmla.HasFreeVars(ln.wff) {
			continue
		}

		prf.lns = append(prf.lns, ln)

		prf.fpcs, prf.facs = reduceFreshConstants(prf, ln.wff)

		tot += 1
	}

	return
}

func (prf *Proof) InsertNewLine(wff *fmla.Wff, rule, purp NDRule, js ...*Line) (tot int) {
	var (
		ln *Line
	)

	ln = prf.NewLine(wff, rule, purp, js...)

	tot = prf.InsertLines(ln)

	return
}

func (prf *Proof) IsRedundant() (is bool) {
	var (
		prfsO    []*Proof
		prfO     *Proof
		wff, bot *fmla.Wff
	)

	prfsO = prf.GetOuterProofs(false)
	prfsO = append(prfsO, prf.prfO.prfsI...)

	for _, prfO = range prfsO {
		if prfO.purp != prf.purp {
			continue
		}

		if fmla.IsIdentical(prfO.lns[0].wff, prf.lns[0].wff) && fmla.IsIdentical(prfO.wffG, prf.wffG) {
			is = true

			break
		}
	}

	if !is {
		// Check if the succesful result would be redundant.
		switch prf.purp {
		case ToIntro:
			wff = fmla.NewBinaryWff(fmla.To, prf.lns[0].wff, prf.wffG)

			is = prf.prfO.WffIsRedundant(wff)
		case NegIntro:
			wff = fmla.NewUnaryWff(fmla.Neg, prf.lns[0].wff)

			is = prf.prfO.WffIsRedundant(wff)
		case ForAllIntro:
			if prf.pvG != 0 {
				wff = fmla.GeneralizePred(fmla.ForAll, prf.wffG, prf.pcA, prf.pvG)
			} else if prf.avG != 0 {
				wff = fmla.GeneralizeArg(fmla.ForAll, prf.wffG, prf.acA, prf.avG)
			} else {
				panic("Illegal proof state: Neither variables are generalizable.")
			}

			is = prf.prfO.WffIsRedundant(wff)
		case ExistsElim:
			is = prf.prfO.WffIsRedundant(prf.wffG)
		case BoxIntro:
			wff = fmla.NewUnaryWff(fmla.Box, prf.lns[0].wff)

			is = prf.prfO.WffIsRedundant(wff)
		case DiamondElim:
			if bot = fmla.NewAtomicWff(fmla.Bot); fmla.IsIdentical(prf.wffG, bot) {
				wff = fmla.NewUnaryWff(fmla.Diamond, prf.lns[0].wff)
				wff = fmla.NewUnaryWff(fmla.Neg, wff)
			} else {
				wff = fmla.NewUnaryWff(fmla.Diamond, prf.wffG)
			}

			is = prf.prfO.WffIsRedundant(wff)
		default:
			panic("Invalid proof purpose.")
		}
	}

	return
}

func (prf *Proof) NewInnerProof(wffG *fmla.Wff, purp NDRule, ln0 *Line) (prfI *Proof) {
	prfI = &Proof{
		wffG: wffG,
		purp: purp,
		open: true,

		lns: []*Line{},

		prfsI: []*Proof{},
		prfO:  prf,

		fpcs: append([]fmla.Predicate{}, prf.fpcs...),
		facs: append([]fmla.Argument{}, prf.facs...),

		pd: prf.pd + 1,
		md: prf.md,
	}

	if ln0.rule != Assumption {
		panic("The first line of an inner proof must be an assumption.")
	} else {
		ln0.prf = prfI
	}

	prfI.lns = append(prfI.lns, ln0)

	switch prfI.purp {
	case ForAllIntro:
		prfI.fpcs, prfI.facs = reduceFreshConstants(prfI, ln0.wff, prfI.wffG)
	case BoxIntro, DiamondElim:
		prfI.fpcs = append([]fmla.Predicate{}, fmla.PredConsts...)
		prfI.facs = append([]fmla.Argument{}, fmla.ArgConsts...)

		prfI.fpcs, prfI.facs = reduceFreshConstants(prfI, ln0.wff)

		prfI.md += 1
	default:
		prfI.fpcs, prfI.facs = reduceFreshConstants(prfI, ln0.wff)
	}

	return
}

func (prf *Proof) InsertInnerProofs(prfsI ...*Proof) (tot int) {
	var (
		prfI *Proof
	)

	for _, prfI = range prfsI {
		if prfI == nil {
			continue
		}

		prf.prfsI = append(prf.prfsI, prfI)

		tot += 1
	}

	return
}

func NewProof(wffG *fmla.Wff, wffsP ...*fmla.Wff) (prf *Proof, synB SynBreadth) {
	var (
		wff *fmla.Wff
		ln  *Line
	)

	prf = &Proof{
		wffG: wffG,
		purp: Solve,
		open: true,

		lns: []*Line{},

		prfsI: []*Proof{},
		prfO:  nil,

		pvG: 0,
		avG: 0,

		fpcs: append([]fmla.Predicate{}, fmla.PredConsts...),
		facs: append([]fmla.Argument{}, fmla.ArgConsts...),

		pd: 0,
		md: 0,
	}

	// Force an initial TopIntro line to meet the requirement that
	// all proofs are non-empty.
	wff = fmla.NewAtomicWff(fmla.Top)

	ln = prf.NewLine(wff, TopIntro, Solve)

	prf.lns = append(prf.lns, ln)

	for _, wff = range wffsP {
		ln = prf.NewLine(wff, Premise, Solve)

		_ = prf.InsertLines(ln)
	}

	wffsP = append(wffsP, wffG)

	synB = GetSyntacticBreadth(wffsP...)

	return
}
