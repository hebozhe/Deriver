package pr

import (
	"Deriver/fmla"
	"slices"
)

func (prf *Proof) AddUniqueLine(wff *fmla.WffTree, rule NDRule, js ...*Line) (added uint) {
	var (
		lenJ       int
		ln         *Line
		j1, j2, j3 *Line
	)

	lenJ = len(js)

	if !correctJCount(rule, 0, lenJ) {
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
		dex: uint(len(prf.lns)),

		wff: fmla.DeepCopy(wff),
		wld: prf.wld,

		rule: rule,
		j1:   j1,
		j2:   j2,
		j3:   j3,
	}

	if !prf.LineIsRedundant(ln) {
		prf.lns = append(prf.lns, ln)

		prf.dom = updateDomain(prf.dom, ln.wff)

		added += 1
	}

	return
}

func (prf *Proof) AddUniqueInnerProof(wff, goal *fmla.WffTree, purp NDRule, js ...*Line) (added uint) {
	var (
		lenJ   int
		ln     *Line
		j1, j2 *Line
		prfI   *Proof
		apc    fmla.Predicate
		aac    fmla.Argument
	)

	lenJ = len(js)

	if !correctJCount(Assumption, purp, lenJ) {
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

		if apc == 0 && aac == 0 {
			panic("No arbitrary predicate or argument constants found.")
		}

		if apc != 0 && aac != 0 {
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
		pid: append(prf.pid, uint(len(prf.inner))),

		purp:   purp,
		hGoal:  fmla.DeepCopy(goal),
		sGoals: []*fmla.WffTree{},

		lns:   []*Line{ln},
		wld:   ln.wld,
		arbPC: apc,
		arbAC: aac,
		dom:   updateDomain(updateDomain(prf.dom, wff), goal),

		inner: []*Proof{},
		outer: prf,
	}

	if !prf.InnerProofIsRedundant(prfI) {
		prf.inner = append(prf.inner, prfI)

		added += 1
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
		if goal == nil || fmla.IsIdentical(prf.hGoal, goal) || slices.ContainsFunc(prf.sGoals, contains) {
			continue
		}

		prf.sGoals = append(prf.sGoals, goal)

		ok = true
	}

	return
}

func (prf *Proof) PopMetSubgoals() (goals []*fmla.WffTree) {
	var (
		ln     *Line
		delete func(g *fmla.WffTree) (has bool)
		met    bool
	)

	if _, _, met = prf.HeadGoalMet(); met {
		prf.sGoals = []*fmla.WffTree{}
	} else {
		delete = func(g *fmla.WffTree) (nix bool) {
			var li *LineInfo = ln.GetLineInfo()

			nix = fmla.IsIdentical(g, li.Wff)

			return
		}

		for _, ln = range prf.lns {
			prf.sGoals = slices.DeleteFunc(prf.sGoals, delete)
		}
	}

	goals = prf.GetAllGoals()

	return
}

func (prf *Proof) MustSelectArbConsts() (apc fmla.Predicate, aac fmla.Argument) {
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

	switch {
	case apc == 0 && aac == 0:
		panic("No arbitrary constants available.")
	case apc != 0 && aac != 0:
		panic("Both arbitrary constant kinds found.")
	}

	return
}

func (prf *Proof) SelectNonArbConsts() (pcs []fmla.Predicate, acs []fmla.Argument) {
	var (
		pc fmla.Predicate
		ac fmla.Argument
	)

	for _, pc = range fmla.PredConsts {
		if prf.dom.pcs[pc] {
			pcs = append(pcs, pc)
		}
	}

	for _, ac = range fmla.ArgConsts {
		if prf.dom.acs[ac] {
			acs = append(acs, ac)
		}
	}

	return
}
