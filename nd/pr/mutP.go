package pr

import (
	"Deriver/fmla"
	"fmt"
	"slices"
)

type PrfMutStatus uint8

const (
	StatusOK PrfMutStatus = iota
	BadRedundant
)

func (prf *Prf) Close() (tot uint) {
	var (
		prfI *Prf
	)

	if prf.open {
		prf.open = false

		tot += uint(len(prf.lns))
	}

	for _, prfI = range prf.prfsI {
		tot += prfI.Close()
	}

	return
}

func resetConstCaches(prf *Prf) (ok bool) {
	var (
		prfI *Prf
	)

	prf.freshPC, prf.freshAC, prf.usedPCs, prf.usedACs = fmla.NoPred, fmla.NoArg, nil, nil

	for prfI = range prf.PrfsI() {
		if prf.depthM == prfI.depthM {
			_ = resetConstCaches(prfI)
		}
	}

	ok = true

	return
}

func (prf *Prf) AddLine(wff *fmla.Wff, rule NDRule, js ...*Line) (ln *Line, pms PrfMutStatus) {
	var (
		lenJ int
	)

	if wff == nil {
		panic("Nil formulas are not allowed.")
	}

	if slices.Contains(js, nil) {
		panic("Nil justifications are not allowed.")
	}

	if lenJ = len(js); !justCountIsCorrect(rule, prf.purp, lenJ) {
		panic(fmt.Sprintf("%d justifications for rule %q, need %d.", lenJ, ruleToString[rule], rulePCount[rule]))
	}

	for lenJ < 2 {
		js = append(js, nil)

		lenJ += 1
	}

	ln = &Line{
		wff:  wff.DeepCopy(),
		rule: rule,
		j1:   js[0],
		j2:   js[1],

		prf: prf,
	}

	switch {
	case prf.HasLine(ln):
		ln, pms = nil, BadRedundant
	default:
		prf.lns, pms = append(prf.lns, ln), StatusOK

		// Successfully adding a line to the proof stales the cached values.
		_ = resetConstCaches(prf)
	}

	return
}

func (prf *Prf) AddPrf(wffA, wffG, wffD *fmla.Wff, purp NDRule, js ...*Line) (prfI *Prf, pms PrfMutStatus) {
	var (
		lenJ int
		lnA  *Line
	)

	switch {
	case wffA == nil:
		panic("Nil assumptions are not allowed.")
	case wffG == nil:
		panic("Nil proof goals are not allowed.")
	case wffD == nil:
		panic("Nil discharge goals are not allowed.")
	}

	if !IsDischargeRule(purp) {
		panic(fmt.Sprintf("Expected discharge rule, got %q.", ruleToString[purp]))
	}

	if slices.Contains(js, nil) {
		panic("Nil justifications are not allowed.")
	}

	if lenJ = len(js); !justCountIsCorrect(Ass, purp, lenJ) {
		panic(fmt.Sprintf("%d justifications for Ass(%q), need %d.", lenJ, ruleToString[purp], reqJustCounts[purp]))
	}

	prfI = &Prf{
		wffG:    wffG.DeepCopy(),
		wffD:    wffD.DeepCopy(),
		depthP:  prf.depthP + 1,
		depthM:  prf.depthM + modalIncrement[purp],
		purp:    purp,
		open:    true,
		lns:     nil, // lnA is populated immediately below.
		prfO:    prf,
		prfsI:   []*Prf{},
		freshPC: fmla.NoPred, // Only populated when a subproof calls for one.
		freshAC: fmla.NoArg,  // Only populated when a subproof calls for one.
	}

	for lenJ < 2 {
		js = append(js, nil)

		lenJ += 1
	}

	lnA = &Line{wff: wffA.DeepCopy(), rule: Ass, j1: js[0], j2: js[1], prf: prfI}

	prfI.lns = []*Line{lnA}

	if prf.HasPrf(prfI, prfI.depthM) {
		prfI, pms = nil, BadRedundant
	} else {
		prf.prfsI, pms = append(prf.prfsI, prfI), StatusOK
	}

	return
}

func popPrfsI(prf *Prf, traceP map[*Prf]bool) (ok bool) {
	var (
		prfI *Prf
	)

	ok = true

	prf.prfsI = slices.DeleteFunc(prf.prfsI, func(prfN *Prf) (nix bool) {
		nix = !traceP[prfN]

		return
	})

	for _, prfI = range prf.prfsI {
		_ = popPrfsI(prfI, traceP)
	}

	return
}

func popLns(prf *Prf, traceJ map[*Line]bool, traceP map[*Prf]bool) (ok bool) {
	var (
		prfI *Prf
	)

	ok = true

	prf.lns = slices.DeleteFunc(prf.lns, func(lnN *Line) (nix bool) {
		// Keep assumptions in the same proof, even if not used,
		// to avoid corrupting the local proof's scope, even if it's not among the justifications.
		nix = !(traceJ[lnN] || (traceP[lnN.prf] && lnN.rule == Ass))

		return
	})

	for _, prfI = range prf.prfsI {
		_ = popLns(prfI, traceJ, traceP)
	}

	return
}

func (prf *Prf) Prune() (ok bool) {
	var (
		lnG    *Line
		traceJ map[*Line]bool
		traceP map[*Prf]bool
	)

	if lnG = prf.LineWithWff(prf.wffG); lnG != nil {
		traceJ, traceP = lnG.TraceJusts(true)

		ok = popPrfsI(prf, traceP) && popLns(prf, traceJ, traceP)
	}

	return
}
