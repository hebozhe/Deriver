package nd

import (
	"Deriver/fmla"
)

type NDRule uint8

// Note: DO NOT adjust the order of these rules,
// as they will play a part in determining the kind of logic
// that is needed to derive a given theorem.
const (
	// Assumpions
	Assume NDRule = iota
	Premise
	Theorem
	// Vacuous
	TopIntro
	// Implicational
	ToIntro
	ToElim
	// Positive
	WedgeIntro
	WedgeElim
	VeeIntro
	VeeElim
	IffIntro
	IffElim
	Reit
	// Minimal
	BotIntro
	NegIntro
	// Intuitionistic
	BotElim
	// Classical
	NegElim
	// N-Order Logic
	ForAllIntro
	ForAllElim
	ExistsIntro
	ExistsElim
	// N-Order Logic with Identity
	IdenIntro
	IdenElim
	// Kripke Logic
	BoxIntro
	BoxElim
	DiamondIntro
	DiamondElim
	// Modal Logic D
	RuleD
	// Modal Logic M
	IntroM
	ElimM
	// Modal Logic 4
	Intro4
	Elim4
	// Modal Logic B
	IntroB
	ElimB
)

var Purposes = []NDRule{
	ToIntro, NegIntro,
	ForAllIntro, ExistsElim,
	BoxIntro, DiamondElim,
}

type WffID string

func GetWffID(step *Step) (id WffID) {
	var s string = fmla.GetWffString(step.Wff)

	id = WffID(s)

	return
}

type Justification struct {
	Rule     NDRule  // What inference rule justifies this step?
	Purpose  NDRule  // If Rule is Assumption, what rule is it meant to facilitate?
	Premises []WffID // Which lines of the proof are applied?
}

type Step struct {
	Wff     *fmla.WffTree
	ID      WffID
	World   uint
	Just    Justification
	ArbPred fmla.Predicate
	ArbArg  fmla.Argument
}

type Proof struct {
	Goal      *fmla.WffTree
	Steps     []*Step
	Subproofs []*Proof
	Parent    *Proof
	Dom       *Domain
}

func NewProof(goal *fmla.WffTree, parent *Proof, steps ...*Step) (prf *Proof) {
	prf = &Proof{
		Goal:      fmla.DeepCopy(goal),
		Steps:     append([]*Step{}, steps...),
		Subproofs: []*Proof{},
		Parent:    parent,
	}

	prf.Dom = GetDomain(prf)

	return
}

func NewVacuousStep(prf *Proof) (step *Step) {
	var (
		last int
	)

	if last = len(prf.Steps) - 1; last == -1 {
		step = &Step{
			Wff:   fmla.NewAtomicWff(fmla.Top),
			World: 0,
			Just: Justification{
				Rule:     TopIntro,
				Purpose:  0,
				Premises: []WffID{},
			},
			ArbPred: 0,
			ArbArg:  0,
		}
	} else {
		step = &Step{
			Wff:     fmla.NewAtomicWff(fmla.Top),
			World:   prf.Steps[last].World,
			ArbPred: prf.Steps[last].ArbPred,
			ArbArg:  prf.Steps[last].ArbArg,
			Just: Justification{
				Rule:     TopIntro,
				Purpose:  0,
				Premises: []WffID{},
			},
		}
	}

	return
}

func AddSubproof(prfA *Proof, wffH, goalH *fmla.WffTree, why NDRule, prems ...*Step) (prfB *Proof, dexH int) {
	var (
		prfH        *Proof
		stepH, prem *Step
	)

	prfH = NewProof(goalH, prfA)

	stepH = NewVacuousStep(prfA)

	stepH.Wff = fmla.DeepCopy(wffH)

	if why == BoxIntro || why == DiamondElim {
		stepH.World += 1
	}

	stepH.Just = Justification{
		Rule:    Assume,
		Purpose: why,
	}

	for _, prem = range prems {
		stepH.Just.Premises = append(stepH.Just.Premises, prem.ID)
	}

	prfH.Steps = append(prfH.Steps, stepH)

	prfA.Subproofs = append(prfA.Subproofs, prfH)

	prfB = prfA

	dexH = len(prfB.Subproofs) - 1

	return
}

func GetVisibleSteps(prf *Proof) (steps []*Step) {
	var (
		curr *Proof
	)

	curr = prf

	for curr != nil {
		steps = append(steps, curr.Steps...)
		curr = curr.Parent
	}

	return
}

func IsRedundant(step *Step, prf *Proof) (is bool) {
	var (
		stepsV []*Step
		stepV  *Step
	)

	stepsV = GetVisibleSteps(prf)

	for _, stepV = range stepsV {
		if is = fmla.Identical(step.Wff, stepV.Wff) && step.World == stepV.World; is {
			break
		}
	}

	return
}

func GetLegalSteps(prf *Proof, step *Step) (stepsL []*Step) {
	panic("Not implemented")
}
