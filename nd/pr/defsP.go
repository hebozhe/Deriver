package pr

import (
	"Deriver/fmla"
	"slices"
)

type Line struct {
	wff        *fmla.WffTree
	rule       NDRule
	j1, j2, j3 *Line
}

type Proof struct {
	wffG   *fmla.WffTree
	purp   NDRule
	isOpen bool

	lns []*Line

	dom *Domain

	hist map[LineHash]bool

	prfsI []*Proof
	prfO  *Proof
}

type LineInfo struct {
	Ln *Line // The line, itself.

	// Information about the line:
	Wff *fmla.WffTree

	Rule       NDRule
	J1, J2, J3 *Line

	// Information about the wff on the line:
	Mop        fmla.Symbol
	SubL, SubR *fmla.WffTree
	MopL, MopR fmla.Symbol // Used frequently for modal rules...

	PV   fmla.Predicate
	AV   fmla.Argument
	Pred fmla.Predicate
	Args []fmla.Argument

	// Information about the proof where the line is:
	WffG   *fmla.WffTree
	Purp   NDRule
	IsOpen bool

	Prf   *Proof
	PrfsI []*Proof
	PrfO  *Proof
}

func getJustificationDependencies(ln *Line) (depsJ map[*Line]bool) {
	var (
		deps map[*Line]bool
		lnJ  *Line
	)

	depsJ = map[*Line]bool{ln: true}

	if ln.j1 != nil {
		deps = getJustificationDependencies(ln.j1)

		for lnJ = range deps {
			depsJ[lnJ] = true
		}
	}

	if ln.j2 != nil {
		deps = getJustificationDependencies(ln.j2)

		for lnJ = range deps {
			depsJ[lnJ] = true
		}
	}

	if ln.j3 != nil {
		deps = getJustificationDependencies(ln.j3)

		for lnJ = range deps {
			depsJ[lnJ] = true
		}
	}

	return
}

func NewLine(wff, wffG *fmla.WffTree, rule, purp NDRule, prfO *Proof, js ...*Line) (ln *Line, prfI *Proof) {
	var (
		lenJ int
	)

	if lenJ = len(js); !isJCountCorrect(rule, purp, lenJ) {
		panic("The number of justifications is wrong.")
	}

	if rule == Assumption && wffG == nil {
		panic("Assumption lines must have a wffG.")
	} else if rule != Assumption && wffG != nil {
		panic("Non-assumption lines must not have a wffG.")
	}

	if rule == Assumption && prfO == nil {
		panic("Assumption lines must have a prfO.")
	}

	ln = &Line{
		wff: fmla.DeepCopy(wff),

		rule: rule,
	}

	switch lenJ {
	case 3:
		ln.j1, ln.j2, ln.j3 = js[0], js[1], js[2]
	case 2:
		ln.j1, ln.j2 = js[0], js[1]
	case 1:
		ln.j1 = js[0]
	default:
	}

	if rule == Assumption {
		prfI = &Proof{
			wffG:   fmla.DeepCopy(wffG),
			purp:   purp,
			isOpen: true,

			lns: []*Line{ln},

			dom: newDomain().updateDomain(wff, wffG),

			hist: map[LineHash]bool{},

			prfsI: []*Proof{},
			prfO:  prfO,
		}

		switch purp {
		case ForAllIntro, ExistsElim:
			prfI.dom.apc, prfI.dom.aac = prfI.dom.findUniqueConstants(prfI.prfO.dom, wff, wffG)
		default:
			prfI.dom.apc, prfI.dom.aac = prfI.prfO.dom.apc, prfI.prfO.dom.aac
		}
	}

	return
}

func (prf *Proof) GetWffG() (wffG *fmla.WffTree) {
	wffG = fmla.DeepCopy(prf.wffG)

	return
}

func (prf *Proof) GetPurpose() (purp NDRule) {
	purp = prf.purp

	return
}

func (prf *Proof) IsOpen() (is bool) {
	is = prf.isOpen

	return
}

func (prf *Proof) InsertLine(ln *Line) (tot int) {
	var (
		lh LineHash
	)

	lh = prf.hashLine(ln)

	if !prf.hist[lh] {
		prf.lns = append(prf.lns, ln)

		prf.hist[lh] = true

		tot = 1
	}

	return
}

func (prf *Proof) InsertInnerProof(prfI *Proof) (tot int) {
	var (
		lenL int
		lh   LineHash
	)

	if lenL = len(prfI.lns); lenL == 0 {
		panic("Inner proofs cannot be empty.")
	} else if prfI.lns[0].rule != Assumption {
		panic("Inner proofs must begin with an assumption.")
	}

	if prfI.wffG == nil {
		panic("Inner proofs must have a wffG.")
	}

	lh = prfI.hashLine(prfI.lns[0])

	if !prfI.prfO.hist[lh] {
		prf.prfsI = append(prf.prfsI, prfI)

		prfI.prfO.hist[lh] = true

		prfI.hist[lh] = true

		tot = 1
	}

	return
}

func (prf *Proof) GetInfo(ln *Line) (li *LineInfo) {
	var (
		has bool
	)

	if has = slices.Contains(prf.lns, ln); !has {
		panic("Cannot get info for line not in the proof.")
	}

	li = &LineInfo{
		// Line information:
		Ln: ln,

		Wff: fmla.DeepCopy(ln.wff),

		Rule: ln.rule,
		J1:   ln.j1,
		J2:   ln.j2,
		J3:   ln.j3,

		// Wff information:
		Mop: fmla.GetWffMop(ln.wff),

		SubL: nil, // Filled in below.
		SubR: nil, // Filled in below.

		MopL: 0, // Filled in below.
		MopR: 0, // Filled in below.

		PV:   0,                 // Filled in below.
		AV:   0,                 // Filled in below.
		Pred: 0,                 // Filled in below.
		Args: []fmla.Argument{}, // Filled in below.

		// Proof information:
		WffG:   fmla.DeepCopy(prf.wffG),
		Purp:   prf.purp,
		IsOpen: prf.isOpen,

		Prf:   prf,
		PrfsI: append([]*Proof{}, prf.prfsI...),
		PrfO:  prf.prfO,
	}

	li.SubL, li.SubR = fmla.GetWffSubformulae(li.Wff)

	if li.SubL != nil {
		li.MopL = fmla.GetWffMop(li.SubL)
	}

	if li.SubR != nil {
		li.MopR = fmla.GetWffMop(li.SubR)
	}

	if li.Mop == fmla.Exists || li.Mop == fmla.ForAll {
		li.PV, li.AV = fmla.GetWffVars(li.Wff)
	}

	if li.Mop == fmla.NoSymbol {
		li.Pred, li.Args, _ = fmla.GetWffPredAndArgs(li.Wff)
	}

	return
}

func (prf *Proof) GetDepth() (d int) {
	if prf.prfO != nil {
		d = 1 + prf.prfO.GetDepth()
	}

	return
}

func (prf *Proof) IsWffGMet() (li *LineInfo, met bool) {
	var (
		ln *Line
	)

	for _, ln = range prf.lns {
		if met = fmla.IsIdentical(prf.wffG, ln.wff); met {
			li = prf.GetInfo(ln)

			break
		}
	}

	return
}

func (prf *Proof) GetLocalLines() (lis []*LineInfo, lenL int) {
	var (
		ln *Line
		li *LineInfo
	)

	for _, ln = range prf.lns {
		li = prf.GetInfo(ln)

		lis = append(lis, li)
	}

	lenL = len(lis)

	return
}

func (prf *Proof) GetLegalLines() (lis []*LineInfo, lenL int) {
	var (
		prfO       *Proof
		li         *LineInfo
		lisO, lisP []*LineInfo
		pv, apc    fmla.Predicate
		av, aac    fmla.Argument
	)

	if prf.isOpen {
		switch prf.purp {
		case ExistsElim:
			lis, _ = prf.GetLocalLines()

			pv, av = fmla.GetWffVars(lis[0].J1.wff)

			prfO = prf.prfO

			apc, aac = prf.GetArbitraryConstants()

			for prfO != nil && prfO.isOpen {
				lisO, _ = prfO.GetLocalLines()

				for _, li = range lisO {
					if pv != 0 && fmla.HasPred(li.Wff, apc) {
						continue
					}

					if av != 0 && fmla.HasArg(li.Wff, aac) {
						continue
					}

					lis = append(lis, li)
				}

				prfO = prfO.prfO
			}
		case BoxIntro, DiamondElim:
			lis, _ = prf.GetLocalLines()

			prfO = prf.prfO

			for prfO != nil && prfO.isOpen {
				lisO, _ = prfO.GetLocalLines()

				for _, li = range lisO {
					if li.Mop != fmla.Box && (li.Mop != fmla.Neg || li.MopL != fmla.Diamond) {
						continue
					}

					lis = append(lis, li)
				}

				if prfO.purp == BoxIntro || prfO.purp == DiamondElim {
					break
				}

				prfO = prfO.prfO
			}
		default:
			prfO = prf.prfO

			for prfO != nil && prfO.isOpen {
				lisO, _ = prfO.GetLocalLines()

				lis = append(lisO, lis...)

				prfO = prfO.prfO
			}
		}
	}

	lisP, _ = prf.GetLocalLines()

	lis = append(lis, lisP...)

	lenL = len(lis)

	return
}

func (prf *Proof) GetLegalSubformulae(op fmla.Symbol) (wffs []*fmla.WffTree, lenW int) {
	var (
		lis  []*LineInfo
		li   *LineInfo
		subs []*fmla.WffTree
	)

	lis, _ = prf.GetLegalLines()
	lis = slices.DeleteFunc(lis, func(li *LineInfo) (nix bool) {
		nix = li.Rule != Premise && li.Rule != Assumption && !fmla.HasOp(li.Wff, op)

		return
	})

	for _, li = range lis {
		subs = fmla.GetAllSubformulae(li.Wff)
		subs = slices.DeleteFunc(subs, func(wff *fmla.WffTree) (nix bool) {
			nix = fmla.GetWffMop(wff) != op

			return
		})

		wffs = append(wffs, subs...)

		if li.WffG != nil {
			subs = fmla.GetAllSubformulae(li.WffG)
			subs = slices.DeleteFunc(subs, func(wff *fmla.WffTree) (nix bool) {
				nix = fmla.GetWffMop(wff) != op

				return
			})

			wffs = append(wffs, subs...)
		}
	}

	lenW = len(wffs)

	return
}

func (prf *Proof) GetFirstLine() (li *LineInfo) {
	li = prf.GetInfo(prf.lns[0])

	return
}

func (prf *Proof) GetOutermostProof() (prfO *Proof) {
	if prf.prfO == nil {
		prfO = prf
	} else {
		prfO = prf.prfO.GetOutermostProof()
	}

	return
}

func (prf *Proof) GetInnerProofs(open bool) (prfsI []*Proof) {
	var (
		prfI   *Proof
		prfsII []*Proof
	)

	for _, prfI = range prf.prfsI {
		if open && !prfI.isOpen {
			continue
		}

		prfsI = append(prfsI, prfI)

		prfsII = prfI.GetInnerProofs(open)

		prfsI = append(prfsI, prfsII...)
	}

	return
}

func (prf *Proof) GetInnermostProofs(open bool) (prfsI []*Proof) {
	var (
		prfs          []*Proof
		prfI          *Proof
		lenI          int
		depthToProofs map[int][]*Proof
		d, maxD       int
	)

	prfs = prf.GetInnerProofs(open)

	if open {
		depthToProofs = map[int][]*Proof{}

		for _, prfI = range prfs {
			if !prfI.isOpen {
				continue
			}

			d = prfI.GetDepth()

			depthToProofs[d] = append(depthToProofs[d], prfI)
		}

		for d = range depthToProofs {
			if maxD < d {
				maxD = d
			}
		}

		if maxD == 0 && prf.isOpen {
			prfsI = []*Proof{prf}
		} else {
			prfsI = depthToProofs[maxD]
		}
	} else {
		for _, prfI = range prfs {
			if lenI = len(prfI.prfsI); 0 < lenI {
				continue
			}

			prfsI = append(prfsI, prfI)
		}

		if lenI = len(prfsI); lenI == 0 {
			prfI = prf.GetOutermostProof()

			prfsI = append(prfsI, prfI)
		}
	}

	return
}

func (prf *Proof) GetLocalConstants() (pcs []fmla.Predicate, acs []fmla.Argument, apc fmla.Predicate, aac fmla.Argument) {
	var (
		pc fmla.Predicate
		ac fmla.Argument
	)

	for _, pc = range fmla.PredConsts {
		if prf.dom.pcs[pc] {
			pcs = append(pcs, pc)
		} else if apc == 0 {
			apc = pc
		}
	}

	for _, ac = range fmla.ArgConsts {
		if prf.dom.acs[ac] {
			acs = append(acs, ac)
		} else if aac == 0 {
			aac = ac
		}
	}

	pcs, acs = fmla.RemoveRedundantEntries(pcs, acs)

	return
}

func (prf *Proof) GetLegalConstants() (pcs []fmla.Predicate, acs []fmla.Argument, apc fmla.Predicate, aac fmla.Argument) {
	var (
		prfO *Proof
		pcsO []fmla.Predicate
		acsO []fmla.Argument
	)

	pcs, acs, apc, aac = prf.GetLocalConstants()

	prfO = prf.prfO

	for prfO != nil {
		pcsO, acsO, _, _ = prfO.GetLocalConstants()

		pcs = append(pcs, pcsO...)
		acs = append(acs, acsO...)

		prfO = prfO.prfO
	}

	pcs, acs = fmla.RemoveRedundantEntries(pcs, acs)

	return
}

func (prf *Proof) GetLocalVariables() (pvs []fmla.Predicate, avs []fmla.Argument) {
	var (
		pv fmla.Predicate
		av fmla.Argument
	)

	for _, pv = range fmla.PredVars {
		if prf.dom.pvs[pv] {
			pvs = append(pvs, pv)
		}
	}

	for _, av = range fmla.ArgVars {
		if prf.dom.avs[av] {
			avs = append(avs, av)
		}
	}

	pvs, avs = fmla.RemoveRedundantEntries(pvs, avs)

	return
}

func (prf *Proof) GetLegalVariables() (pvs []fmla.Predicate, avs []fmla.Argument) {
	var (
		prfO *Proof
		pvsO []fmla.Predicate
		avsO []fmla.Argument
	)

	pvs, avs = prf.GetLocalVariables()

	prfO = prf.prfO

	for prfO != nil {
		pvsO, avsO = prfO.GetLocalVariables()

		pvs = append(pvs, pvsO...)
		avs = append(avs, avsO...)

		prfO = prfO.prfO
	}

	pvs, avs = fmla.RemoveRedundantEntries(pvs, avs)

	return
}

func (prf *Proof) GetArbitraryConstants() (apc fmla.Predicate, aac fmla.Argument) {
	apc, aac = prf.dom.apc, prf.dom.aac

	return
}

func (prf *Proof) CloseProof() (ok bool) {
	var (
		prfI *Proof
	)

	prf.isOpen = false

	for _, prfI = range prf.prfsI {
		_ = prfI.CloseProof()
	}

	return
}

func (prf *Proof) FindJustfyingInnerProof(ln *Line) (prfI *Proof, ok bool) {
	if ok = isDischargeRule(ln.rule); ok {
		switch ln.rule {
		case ToIntro, NegIntro, ForAllIntro, BoxIntro: // Two-line justifications.
			for _, prfI = range prf.prfsI {
				if prfI.lns[0] == ln.j1 {
					break
				}
			}
		case ExistsElim, DiamondElim: // Three-line justifications.
			for _, prfI = range prf.prfsI {
				if prfI.lns[0] == ln.j2 {
					break
				}
			}
		default:
			panic("Unknown discharge rule.")
		}
	}

	ok = prfI != nil

	return
}

func (prf *Proof) FlattenProof() (lis []*LineInfo) {
	var (
		prfI            *Proof
		lisI            []*LineInfo
		lenI, dex, lenL int
		li              *LineInfo
	)

	lis, lenL = prf.GetLocalLines()

	if lenI = len(prf.prfsI); 0 < lenI {
	FLATTENPROOF_OUTER:
		for _, prfI = range prf.prfsI {
			lisI = prfI.FlattenProof()

			if lenI = len(lisI); 0 == lenI {
				continue
			}

			for dex, li = range lis {
				if !isDischargeRule(li.Rule) {
					continue
				}

				switch li.Rule {
				case ToIntro, NegIntro, ForAllIntro, BoxIntro: // Two-line justifications.
					if lisI[0].Ln == li.J1 {
						lis = slices.Insert(lis, dex, lisI...)

						continue FLATTENPROOF_OUTER
					}

				case ExistsElim, DiamondElim: // Three-line justifications.
					if lisI[0].Ln == li.J2 {
						lis = slices.Insert(lis, dex, lisI...)

						continue FLATTENPROOF_OUTER
					}
				default:
					panic("Unrecognized discharge rule.")
				}
			}

			if dex == lenL {
				lis = append(lis, lisI...)
			}
		}
	}

	return
}

func (prf *Proof) IsTheorem(ln *Line) (is bool) {
	var (
		prfJ *Proof
		lis  []*LineInfo
		li   *LineInfo
	)

	if is = isDischargeRule(ln.rule); is {
		if prfJ, is = prf.FindJustfyingInnerProof(ln); is {
			lis = prfJ.FlattenProof()

			is = true

			for _, li = range lis {
				if is = is &&
					(li.J1 == nil || slices.ContainsFunc(lis, func(liN *LineInfo) (has bool) { has = liN.Ln == li.J1; return })) &&
					(li.J2 == nil || slices.ContainsFunc(lis, func(liN *LineInfo) (has bool) { has = liN.Ln == li.J2; return })) &&
					(li.J3 == nil || slices.ContainsFunc(lis, func(liN *LineInfo) (has bool) { has = liN.Ln == li.J3; return })); !is {
					break
				}
			}
		}
	}

	return
}

func (prf *Proof) IsJustifiedByLine(lnA *Line, lnJ *Line) (is bool) {
	var (
		depsJ map[*Line]bool
	)

	depsJ = getJustificationDependencies(lnA)

	_, is = depsJ[lnJ]

	return
}

func NewProof(goal *fmla.WffTree, prems ...*fmla.WffTree) (prf *Proof) {
	var (
		wff *fmla.WffTree
		ln  *Line
		lh  LineHash
	)

	wff = fmla.NewAtomicWff(fmla.Top)

	ln, _ = NewLine(wff, nil, TopIntro, 0, nil)

	prf = &Proof{
		wffG:   fmla.DeepCopy(goal),
		purp:   Solve,
		isOpen: true,

		lns: []*Line{ln},

		dom: newDomain().updateDomain(goal).updateDomain(prems...),

		hist: map[LineHash]bool{},

		prfsI: []*Proof{},
		prfO:  nil,
	}

	lh = prf.hashLine(ln)

	prf.hist[lh] = true

	for _, wff = range prems {
		ln, _ = NewLine(wff, nil, Premise, 0, nil)

		_ = prf.InsertLine(ln)
	}

	return
}
