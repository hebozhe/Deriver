package pr

import (
	"Deriver/fmla"
)

type World uint

type Line struct {
	wff *fmla.WffTree // The wff on the line.
	wld World         // The world in which the wff holds.

	rule       NDRule // The rule used to derive the wff.
	j1, j2, j3 *Line  // The lines whose wffs justify the wff.
}

type LineInfo struct {
	Wff, SubL, SubR *fmla.WffTree
	Mop             fmla.Symbol
	Wld             World
	Rule            NDRule
	J1, J2, J3      *Line
}

type Proof struct {
	purp  NDRule          // The purpose of the proof.
	goals []*fmla.WffTree // The goal of the proof.
	lns   []*Line         // The lines in the proof.
	wld   World           // The world in which the proof holds.
	arbPC fmla.Predicate  // The arbitrary predicate constant introduced, if any.
	arbAC fmla.Argument   // The arbitrary argument constant introduced, if any.
	dom   *Domain         // The quantificational domain of the proof.

	inner []*Proof // The inner, "child" proofs.
	outer *Proof   // The outer, "parent" proof.
}

type ProofInfo struct {
	Purp  NDRule
	Goals []*fmla.WffTree
	Lns   []*Line
	Wld   World
	ArbPC fmla.Predicate
	ArbAC fmla.Argument
	Dom   *Domain

	Inner []*Proof
	Outer *Proof
}

func GetLineInfo(ln *Line) (li *LineInfo) {
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

	li.Mop = fmla.GetWffMainOperator(ln.wff)

	li.SubL, li.SubR = fmla.GetWffSubformulae(ln.wff)

	return
}

func GetProofInfo(prf *Proof) (pi *ProofInfo) {
	var (
		goal *fmla.WffTree
	)

	pi = &ProofInfo{
		Purp:  prf.purp,
		Goals: []*fmla.WffTree{},
		Lns:   prf.lns,
		Wld:   prf.wld,
		ArbPC: prf.arbPC,
		ArbAC: prf.arbAC,
		Dom:   newDomain(),
		Inner: append([]*Proof{}, prf.inner...),
		Outer: prf.outer,
	}

	for _, goal = range prf.goals {
		goal = fmla.DeepCopy(goal)

		pi.Goals = append(pi.Goals, goal)
	}

	return
}

func AddGoalsToProof(prfA *Proof, goals ...*fmla.WffTree) (prfB *Proof) {
	var (
		goal *fmla.WffTree
	)

	for _, goal = range goals {
		goal = fmla.DeepCopy(goal)

		prfA.goals = append(prfA.goals, goal)
	}

	prfB = prfA

	return
}

func AddLineToProof(prfA *Proof, wff *fmla.WffTree, rule NDRule, js ...*Line) (prfB *Proof) {
	var (
		lenJ           int
		ln, j1, j2, j3 *Line
	)

	if lenJ = len(js); !correctJCount(rule, 0, lenJ) {
		panic("Incorrect number of justification lines.")
	}

	switch lenJ {
	case 1:
		j1 = js[0]
	case 2:
		j1, j2 = js[0], js[1]
	case 3:
		j1, j2, j3 = js[0], js[1], js[2]
	}

	ln = &Line{
		wff:  wff,
		wld:  prfA.wld,
		rule: rule,
		j1:   j1,
		j2:   j2,
		j3:   j3,
	}

	prfA.lns = append(prfA.lns, ln)

	// Update the domain within the proof to account for the new wff.
	prfA.dom = updateDomain(prfA.dom, wff)

	prfB = prfA

	return
}

func NewProof(goal *fmla.WffTree, ps ...*fmla.WffTree) (prf *Proof) {
	var (
		lenP, dex int
		wff       *fmla.WffTree
	)

	goal, lenP = fmla.DeepCopy(goal), len(ps)

	prf = &Proof{
		purp:  Solve,
		goals: []*fmla.WffTree{goal},
		lns:   make([]*Line, lenP+1),
		wld:   0,
		dom:   newDomain(),

		inner: []*Proof{},
		outer: nil,
	}

	// To ensure that every proof is non-empty, add a top line with TopIntro,
	// which is permissible in any proof with no premises.
	prf.lns[0] = &Line{
		wff:  fmla.NewAtomicWff(fmla.Top),
		wld:  0,
		rule: TopIntro,
		j1:   nil,
		j2:   nil,
		j3:   nil,
	}

	// From there, add the premises to the proof, if any exist.
	for dex, wff = range ps {
		wff = fmla.DeepCopy(ps[dex])

		prf.lns[dex+1] = &Line{
			wff:  wff,
			wld:  0,
			rule: Premise,
			j1:   nil,
			j2:   nil,
			j3:   nil,
		}
	}

	return
}

func AddInnerProofToProof(prfA *Proof, wff, goal *fmla.WffTree, purp NDRule, js ...*Line) (prfB *Proof) {
	var (
		lenJ       int
		lnH        *Line
		prfH       *Proof
		j1, j2, j3 *Line
	)

	if lenJ = len(js); !correctJCount(Assumption, purp, lenJ) {
		panic("Incorrect number of justification lines.")
	}

	switch lenJ {
	case 1:
		j1 = js[0]
	case 2:
		j1, j2 = js[0], js[1]
	case 3:
		j1, j2, j3 = js[0], js[1], js[2]
	}

	lnH = &Line{
		wff:  wff,
		wld:  prfA.wld,
		rule: Assumption,
		j1:   j1,
		j2:   j2,
		j3:   j3,
	}

	goal = fmla.DeepCopy(goal)

	prfH = &Proof{
		purp:  purp,
		goals: []*fmla.WffTree{goal},
		lns:   []*Line{lnH},
		wld:   prfA.wld,
		arbPC: 0,
		arbAC: 0,
		dom:   newDomain(),

		inner: []*Proof{},
		outer: prfA,
	}

	// The claimed domain of prfH is the domain of prfA plus the constants in wff.
	prfH.dom = updateDomain(prfA.dom, wff)

	switch purp {
	case DiamondElim, BoxIntro:
		prfH.wld += 1
		prfH.lns[0].wld = prfH.wld
	case ExistsElim, ForAllIntro:
		prfH.arbPC, prfH.arbAC = findArbConsts(prfH.dom, prfA.dom)

		if prfH.arbPC == 0 && prfH.arbAC == 0 {
			panic("No arbitrary constants in proof that requires one.")
		}
	}

	prfA.inner = append(prfA.inner, prfH)

	prfB = prfA

	return
}

func GetAdmissibleLines(prf *Proof) (lns []*Line) {
	var (
		wld  World
		prfO *Proof
		ln   *Line
		mop  fmla.Symbol
	)

	wld = prf.wld

	prfO = prf

	for prfO != nil {
		for _, ln = range prfO.lns {
			if ln.wld == wld {
				lns = append(lns, ln)

				continue
			}

			// If the line is a box in an immediately lower world,
			// it is available.
			mop = fmla.GetWffMainOperator(ln.wff)

			if ln.wld+1 == wld && mop == fmla.Box {
				lns = append(lns, ln)
			}
		}

		prfO = prfO.outer
	}

	return
}
