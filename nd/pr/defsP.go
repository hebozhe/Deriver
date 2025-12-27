package pr

import (
	"Deriver/fmla"
	"slices"
)

type world uint

type Line struct {
	wff *fmla.WffTree // The wff on the line.
	wld world         // The world in which the wff holds.

	rule       NDRule // The rule used to derive the wff.
	j1, j2, j3 *Line  // The lines whose wffs justify the wff.
}

type LineInfo struct {
	Wff        *fmla.WffTree
	Mop        fmla.Symbol
	PVar       fmla.Predicate
	AVar       fmla.Argument
	SubL, SubR *fmla.WffTree
	Wld        world

	Rule       NDRule
	J1, J2, J3 *Line
}

type Proof struct {
	purp   NDRule          // The purpose of the proof, the sought rule to apply.
	iGoal  *fmla.WffTree   // The main formula to be proven via an introduction rule.
	sGoals []*fmla.WffTree // Subgoals to accomplish other rules elsewhere.

	lns   []*Line        // The lines of the proof.
	wld   world          // The world in which the proof holds.
	arbPC fmla.Predicate // The arbitrary predicate constant introduced, if any.
	arbAC fmla.Argument  // The arbitrary argument constant introduced, if any.
	dom   *domain        // The quantificational domain of the proof.

	inner []*Proof // The inner subproofs of the proof.
	outer *Proof   // The outer subproof of the proof, if this is an inner proof.
}

func (ln *Line) GetLineInfo() (li *LineInfo) {
	li = &LineInfo{
		Wff:  fmla.DeepCopy(ln.wff),
		Mop:  fmla.NoSymbol,
		SubL: nil,
		SubR: nil,
		Wld:  ln.wld,

		Rule: ln.rule,
		J1:   ln.j1,
		J2:   ln.j2,
		J3:   ln.j3,
	}

	li.Mop, li.PVar, li.AVar = fmla.GetWffMopAndVars(li.Wff)

	li.SubL, li.SubR = fmla.GetWffSubformulae(li.Wff)

	return
}

func (prf *Proof) MustAddNewLine(wff *fmla.WffTree, rule NDRule, js ...*Line) (ok bool) {
	var (
		lenJ       int
		ln         *Line
		j1, j2, j3 *Line
	)

	lenJ = len(js)

	if ok = correctJCount(rule, 0, lenJ); !ok {
		panic("Incorrect number of justification lines.")
	}

	switch lenJ {
	case 0:
		j1, j2, j3 = nil, nil, nil
	case 1:
		j1, j2, j3 = js[0], nil, nil
	case 2:
		j1, j2, j3 = js[0], js[1], nil
	case 3:
		j1, j2, j3 = js[0], js[1], js[2]
	default:
		panic("Incorrect number of justification lines.")
	}

	ln = &Line{
		wff: fmla.DeepCopy(wff),
		wld: prf.wld,

		rule: rule,
		j1:   j1,
		j2:   j2,
		j3:   j3,
	}

	prf.lns = append(prf.lns, ln)

	prf.dom = updateDomain(prf.dom, ln.wff)

	return
}

func (prf *Proof) MustAddNewInnerProof(wff, goal *fmla.WffTree, purp NDRule, js ...*Line) (ok bool) {
	var (
		lenJ   int
		ln     *Line
		j1, j2 *Line
		prfI   *Proof
		apc    fmla.Predicate
		aac    fmla.Argument
	)

	lenJ = len(js)

	if ok = correctJCount(Assumption, purp, lenJ); !ok {
		panic("Incorrect number of justification lines.")
	}

	switch lenJ {
	case 0:
		j1, j2 = nil, nil
	case 1:
		j1, j2 = js[0], nil
	case 2:
		j1, j2 = js[0], js[1]
	default:
		panic("Incorrect number of justification lines.")
	}

	ln = &Line{
		wff: fmla.DeepCopy(wff),
		wld: prf.wld,

		rule: Assumption,
		j1:   j1,
		j2:   j2,
		j3:   nil,
	}

	switch purp {
	case ForAllIntro:
		apc, aac = findArbConsts(prf.dom, goal)

		if ok = apc != 0 || aac != 0; !ok {
			panic("No arbitrary predicate or argument constants found.")
		}

		if ok = !(apc != 0 && aac != 0); !ok {
			panic("Both arbitrary predicate and argument constants found.")
		}
	case ExistsElim:
		apc, aac = findArbConsts(prf.dom, wff)

		if apc == 0 && aac == 0 {
			panic("No arbitrary predicate or argument constants found.")
		}

		if !(apc == 0 || aac == 0) {
			panic("Both arbitrary predicate and argument constants found.")
		}
	case BoxIntro, DiamondElim:
		ln.wld += 1
	}

	prfI = &Proof{
		purp:   purp,
		iGoal:  fmla.DeepCopy(goal),
		sGoals: []*fmla.WffTree{},

		lns:   []*Line{ln},
		wld:   ln.wld,
		arbPC: apc,
		arbAC: aac,
		dom:   updateDomain(updateDomain(prf.dom, wff), goal),

		inner: []*Proof{},
		outer: prf,
	}

	prf.inner = append(prf.inner, prfI)

	return
}

func NewBaseProof(goal *fmla.WffTree, prems ...*fmla.WffTree) (prf *Proof) {
	var (
		ln   *Line
		prem *fmla.WffTree
	)

	prf = &Proof{
		purp:   Solve, // Only the base proof has Solve as a purpose.
		iGoal:  fmla.DeepCopy(goal),
		sGoals: []*fmla.WffTree{},

		lns:   []*Line{},
		wld:   0,
		arbPC: 0,
		arbAC: 0,
		dom:   updateDomain(newDomain(), goal),

		inner: []*Proof{},
		outer: nil,
	}

	// As a rule, lns can never be empty, so TopIntro is applied vacuously
	// when no other wff needs to be introduced for a proof or subproof.
	ln = &Line{
		wff: fmla.NewAtomicWff(fmla.Top),
		wld: 0,

		rule: TopIntro,
		j1:   nil,
		j2:   nil,
		j3:   nil,
	}

	prf.lns = append(prf.lns, ln)

	for _, prem = range prems {
		ln = &Line{
			wff: fmla.DeepCopy(prem),
			wld: 0,

			rule: Premise,
			j1:   nil,
			j2:   nil,
			j3:   nil,
		}

		prf.lns = append(prf.lns, ln)
	}

	return
}

func (prf *Proof) GetLocalLines() (lns []*Line) {
	lns = append(lns, prf.lns...)

	return
}

func (prf *Proof) GetLegalLines() (lns []*Line) {
	var (
		prfO *Proof
		ln   *Line
		mop  fmla.Symbol
	)

	lns = append(lns, prf.lns...)

	prfO = prf.outer

	for prfO != nil {
		for _, ln = range prfO.lns {
			if ln.wld == prf.wld {
				lns = append(lns, ln)

				continue
			}

			if mop = fmla.GetWffMop(ln.wff); mop == fmla.Box && ln.wld+1 == prf.wld {
				lns = append(lns, ln)
			}

		}

		prfO = prfO.outer
	}

	return
}

func (prf *Proof) GetInnerProofs(purp NDRule) (prfsI []*Proof) {
	var (
		prfI *Proof
	)

	for _, prfI = range prf.inner {
		if prfI.purp == purp {
			prfsI = append(prfsI, prfI)
		}
	}

	return
}

func (prf *Proof) IntroGoalMet() (ln0, lnX *Line, met bool) {
	var (
		ln *Line
	)

	for _, ln = range prf.lns {
		if met = fmla.IsIdentical(ln.wff, prf.iGoal); met {
			ln0, lnX = prf.lns[0], ln

			break
		}
	}

	return
}

func (prf *Proof) ExtendSubgoals(goals ...*fmla.WffTree) (ok bool) {
	var (
		contains func(g *fmla.WffTree) (has bool)
		goal     *fmla.WffTree
	)

	contains = func(g *fmla.WffTree) (has bool) {
		has = fmla.IsIdentical(g, goal)

		return
	}

	for _, goal = range goals {
		if goal == nil || fmla.IsIdentical(prf.iGoal, goal) || slices.ContainsFunc(prf.sGoals, contains) {
			continue
		}

		prf.sGoals = append(prf.sGoals, goal)
	}

	return
}

func (prf *Proof) MeetsGoal(wff *fmla.WffTree) (met bool) {
	var (
		contains func(g *fmla.WffTree) (has bool)
	)

	contains = func(g *fmla.WffTree) (has bool) {
		has = fmla.IsIdentical(g, wff)

		return
	}

	met = fmla.IsIdentical(wff, prf.iGoal) || slices.ContainsFunc(prf.sGoals, contains)

	return
}

func (prf *Proof) GetAllGoals() (goals []*fmla.WffTree) {
	goals = []*fmla.WffTree{prf.iGoal}
	goals = append(goals, prf.sGoals...)

	return
}
