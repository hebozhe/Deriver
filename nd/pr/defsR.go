package pr

type NDRule uint8

// Note: DO NOT adjust the order of these rules,
// as they will play a part in determining the kind of logic
// that is needed to derive a given theorem.
const (
	Solve NDRule = iota // This is a vacuous purpose for the base proof.
	Premise
	Theorem
	// Assumpions
	Assumption
	// Implicational Propositional Logic (TPL)
	TopIntro
	ToIntro
	ToElim
	Reiteration
	// Positive Propositional Logic (PPL)
	WedgeIntro
	WedgeElim
	VeeIntro
	VeeElim
	IffIntro
	IffElim
	// Minimal Propositional Logic (MPL)
	BotIntro
	NegIntro
	// Intuitionistic Propositional Logic (IPL)
	BotElim
	// Classical Propositional Logic (CPL)
	NegElim
	// N-Order Quantification Logic (QL)
	ForAllIntro
	ForAllElim
	ExistsIntro
	ExistsElim
	// N-Order Logic with Identity (QLi)
	EqualsIntro
	EqualsElim
	// Modal Logic
	BoxIntro
	BoxElim
	DiamondElim
	DiamondIntro
	// Modal Logic K
	IntroK
	// Modal Logic D (K+D)
	ElimD
	// Modal Logic M (K+M)
	IntroM
	ElimM
	// Modal Logic 4 (K+4)
	Intro4
	Elim4
	// Modal Logic B (K+B)
	IntroB
	ElimB
)

var purposePCount map[NDRule]int = map[NDRule]int{
	// Propositional logics:
	ToIntro:  0,
	NegIntro: 0,
	// Quantificational logics:
	ForAllIntro: 0,
	ExistsElim:  1, // The line that has existential quantifier.
	// Modal logics:
	BoxIntro:    0,
	DiamondElim: 1, // The line that has the diamond operator.
}

var rulePCount map[NDRule]int = map[NDRule]int{
	Premise:      0,
	Theorem:      0,
	TopIntro:     0,
	ToIntro:      2,
	ToElim:       2,
	WedgeIntro:   2,
	WedgeElim:    1,
	VeeIntro:     1,
	VeeElim:      3,
	IffIntro:     2,
	IffElim:      1,
	Reiteration:  1,
	BotIntro:     2,
	BotElim:      1,
	NegIntro:     2,
	NegElim:      1,
	ForAllIntro:  2,
	ForAllElim:   1,
	ExistsIntro:  1,
	ExistsElim:   3,
	EqualsIntro:  0,
	EqualsElim:   2,
	BoxIntro:     2,
	BoxElim:      1,
	DiamondElim:  3,
	DiamondIntro: 1,
	IntroK:       1,
	ElimD:        1,
	IntroM:       1,
	ElimM:        1,
	Intro4:       1,
	Elim4:        1,
	IntroB:       1,
	ElimB:        1,
}

func isJCountCorrect(rule, purp NDRule, lenJ int) (is bool) {
	var (
		lenC int
	)

	if rule == Assumption {
		if lenC, is = purposePCount[purp]; is {
			is = lenJ == lenC
		}
	} else {
		lenC = rulePCount[rule]

		is = lenJ == lenC
	}

	return
}

func isDischargeRule(rule NDRule) (is bool) {
	_, is = purposePCount[rule]

	return
}
