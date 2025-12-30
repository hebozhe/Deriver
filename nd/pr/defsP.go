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
	hGoal  *fmla.WffTree   // The head goal, the main formula to be proven via an introduction rule.
	sGoals []*fmla.WffTree // Subgoals, wffs to prove to apply other rules elsewhere.

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

func (prf *Proof) GetFirstLineAndPurpose() (ln0 *Line, purp NDRule) {
	ln0 = prf.lns[0]

	purp = prf.purp

	return
}

func (prf *Proof) GetAllGoals() (goals []*fmla.WffTree) {
	goals = []*fmla.WffTree{prf.hGoal}
	goals = append(goals, prf.sGoals...)

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
			mop = fmla.GetWffMop(ln.wff)

			if ln.wld == prf.wld && mop != fmla.Box {
				lns = append(lns, ln)

				continue
			}

			if ln.wld+1 == prf.wld && mop == fmla.Box {
				lns = append(lns, ln)
			}

		}

		prfO = prfO.outer
	}

	return
}

func (prf *Proof) LineIsRedundant(ln *Line) (is bool) {
	var (
		lns []*Line
	)

	lns = prf.GetLegalLines()

	is = slices.ContainsFunc(lns, func(l *Line) (has bool) {
		has = fmla.IsIdentical(l.wff, ln.wff) &&
			l.wld == ln.wld &&
			l.rule == ln.rule &&
			l.j1 == ln.j1 &&
			l.j2 == ln.j2 &&
			l.j3 == ln.j3

		return
	})

	return
}

func (prf *Proof) InnerProofIsRedundant(prfI *Proof) (is bool) {
	is = slices.ContainsFunc(prf.inner, func(p *Proof) (has bool) {
		has = p.purp == prfI.purp &&
			fmla.IsIdentical(p.lns[0].wff, prfI.lns[0].wff) &&
			fmla.IsIdentical(p.hGoal, prfI.hGoal) &&
			p.wld == prfI.wld &&
			p.arbPC == prfI.arbPC &&
			p.arbAC == prfI.arbAC

		return
	})

	return
}

func (prf *Proof) GetArbConsts() (apc fmla.Predicate, aac fmla.Argument) {
	apc, aac = prf.arbPC, prf.arbAC

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

func NewBaseProof(goal *fmla.WffTree, prems ...*fmla.WffTree) (prf *Proof) {
	var (
		ln   *Line
		prem *fmla.WffTree
	)

	prf = &Proof{
		purp:   Solve, // Only the base proof has Solve as a purpose.
		hGoal:  fmla.DeepCopy(goal),
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

		if !prf.LineIsRedundant(ln) {
			prf.lns = append(prf.lns, ln)
		}
	}

	return
}

func (prf *Proof) HeadGoalMet() (ln0, lnX *Line, met bool) {
	var (
		ln *Line
	)

	for _, ln = range prf.lns {
		if met = fmla.IsIdentical(ln.wff, prf.hGoal); met {
			ln0, lnX = prf.lns[0], ln

			break
		}
	}

	return
}

func (prf *Proof) MeetsAnyGoal(wff *fmla.WffTree) (met bool) {
	var (
		contains func(g *fmla.WffTree) (has bool)
	)

	contains = func(g *fmla.WffTree) (has bool) {
		has = fmla.IsIdentical(g, wff)

		return
	}

	met = fmla.IsIdentical(wff, prf.hGoal) || slices.ContainsFunc(prf.sGoals, contains)

	return
}

func (prf *Proof) LineWorldIsProofWorld(ln *Line) (is bool) {
	is = ln.wld == prf.wld

	return
}
