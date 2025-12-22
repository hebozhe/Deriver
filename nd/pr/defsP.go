package pr

import (
	"Deriver/fmla"
	"slices"
)

type World uint

type Step struct {
	// The first two fields constitute the content of a proof step.
	wff *fmla.WffTree // This is the wff of the step.
	w   World         // This is the world of the step.

	// The last three fields constitute the justification of a proof step.
	rule NDRule   // This is the inference rule that was applied to a step.
	purp NDRule   // If Rule is Assumption, this is the sought rule to execute on this subproof.
	app  [3]*Step // If there is a justification for the rule, these are the steps that allowed the applied rule.
}

type Proof struct {
	goals     []*fmla.WffTree // These are the goals of the proof.
	steps     []*Step         // These are the steps to the proof.
	subproofs []*Proof        // If the proof requires subproofs, these are them.
	parent    *Proof          // If this is a subproof, this is its parent.
	dom       *Domain         // This is the domain of the proof.
}

func GetWff(step *Step) (wff *fmla.WffTree) {
	wff = step.wff

	return
}

func GetWorld(step *Step) (w World) {
	w = step.w

	return
}

func GetWorldAtPoof(prf *Proof) (w World) {
	w = prf.steps[0].w

	return
}

func GetContent(step *Step) (wff *fmla.WffTree, w World) {
	wff, w = step.wff, step.w

	return
}

func GetRule(step *Step) (rule NDRule) {
	rule = step.rule

	return
}

func GetPurpose(step *Step) (purp NDRule) {
	purp = step.purp

	return
}

func GetApplication(step *Step) (from [3]*Step) {
	from = step.app

	return
}

func GetJustification(step *Step) (rule NDRule, purp NDRule, from [3]*Step) {
	rule = step.rule

	purp = step.purp

	from = step.app

	return
}

func GetGoals(prf *Proof) (goals []*fmla.WffTree) {
	goals = prf.goals

	return
}

type ProofScope uint

const (
	LocalScope ProofScope = iota + 1
	VisibleScope
	LegalScope
)

func GetSteps(prf *Proof, scope ProofScope) (steps []*Step) {
	var (
		prfP *Proof
		w    World
	)

	switch scope {
	case LocalScope:
		steps = append(steps, prf.steps...)
	case VisibleScope:
		prfP = prf

		for prfP != nil {
			steps = append(steps, prfP.steps...)

			prfP = prfP.parent
		}
	case LegalScope:
		w = prf.steps[0].w

		steps = GetSteps(prf, VisibleScope)

		steps = slices.DeleteFunc(steps, func(st *Step) (nix bool) {
			var (
				conS fmla.Connective
			)

			conS, _, _ = fmla.GetWffMainOperator(st.wff)

			nix = !(st.w == w || (st.w+1 == w && conS == fmla.Box))

			return
		})
	}

	return
}

func GetSubproofs(prf *Proof) (sprfs []*Proof) {
	sprfs = prf.subproofs

	return
}

func NewStep(wff *fmla.WffTree, w World, rule NDRule, purp NDRule, stepsF ...*Step) (stepN *Step) {
	var (
		lenF int
		from [3]*Step
	)

	wff = fmla.DeepCopy(wff)

	lenF = len(stepsF)

	switch lenF {
	case 0:
		from = [3]*Step{}
	case 1:
		from = [3]*Step{stepsF[0], nil, nil}
	case 2:
		from = [3]*Step{stepsF[0], stepsF[1], nil}
	case 3:
		from = [3]*Step{stepsF[0], stepsF[1], stepsF[2]}
	default:
		panic("Too many premises for a step justification.")
	}

	stepN = &Step{
		wff:  wff,
		w:    w,
		rule: rule,
		purp: purp,
		app:  from,
	}

	return
}

func NewBaseProof(goal *fmla.WffTree, pwffs ...*fmla.WffTree) (prf *Proof) {
	var (
		Twff, pwff *fmla.WffTree
		step       *Step
	)

	prf = &Proof{}

	prf.goals = fmla.AllSubformulae(goal)

	Twff = fmla.NewAtomicWff(fmla.Top)

	step = NewStep(Twff, 0, TopIntro, 0)

	prf.steps = append(prf.steps, step)

	for _, pwff = range pwffs {
		step = NewStep(pwff, 0, Premise, 0)

		prf.steps = append(prf.steps, step)
	}

	prf.dom = newDomain(prf.steps...)

	return
}

func AddNewSubproof(prfA *Proof, wffH, goalH *fmla.WffTree, purp NDRule) (prfB *Proof) {
	var (
		prfH  *Proof
		stepH *Step
	)

	prfH = &Proof{
		goals:     fmla.AllSubformulae(goalH),
		steps:     []*Step{},
		subproofs: []*Proof{},
		parent:    prfA,
		dom:       prfA.dom,
	}

	switch purp {
	case ToIntro, NegIntro:
		stepH = NewStep(wffH, prfA.steps[0].w, Assumption, purp)
	case ForAllIntro, ExistsElim:
		stepH = NewStep(wffH, prfA.steps[0].w, Assumption, purp)
	case BoxIntro, DiamondElim:
		stepH = NewStep(wffH, prfA.steps[0].w+1, Assumption, purp)

		prfH.dom = extendDomain(prfH.dom, stepH)
	default:
		panic("Unrecognized purpose for a subproof.")
	}

	prfH.steps = append(prfH.steps, stepH)

	prfA.subproofs = append(prfA.subproofs, prfH)

	prfB = prfA

	return
}
