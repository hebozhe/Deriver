package pr

type NDRule uint8

// Note: DO NOT adjust the order of these rules,
// as they will play a part in determining the kind of logic
// that is needed to derive a given theorem.
const (
	Solve NDRule = 0 // This is a vacuous purpose for the base proof.
	// Assumpions
	Assumption NDRule = iota + 1
	Premise
	Theorem
	// Vacuous Propositional Logic (VPL)
	TopIntro
	// Implicational Propositional Logic (TPL)
	ToIntro
	ToElim
	// Positive Propositional Logic (PPL)
	WedgeIntro
	WedgeElim
	VeeIntro
	VeeElim
	IffIntro
	IffElim
	Reit
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
	// Intuitionistic Modal Logic K (+IK)
	BoxIntro
	BoxElim
	DiamondElim
	// Classical Modal Logic K (+CK)
	DiamondIntro
	// Modal Logic D (K+D)
	IntroD
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

var purposes = [6]NDRule{
	ToIntro, NegIntro,
	ForAllIntro, ExistsElim,
	BoxIntro, DiamondElim,
}

var purposePCount map[NDRule]int = map[NDRule]int{
	ToIntro:     0,
	NegIntro:    0,
	ForAllIntro: 0,
	ExistsElim:  1,
	BoxIntro:    0,
	DiamondElim: 1,
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
	Reit:         1,
	BotIntro:     2,
	BotElim:      1,
	NegIntro:     1,
	NegElim:      1,
	ForAllIntro:  2,
	ForAllElim:   1,
	ExistsIntro:  1,
	ExistsElim:   3,
	EqualsIntro:  0,
	EqualsElim:   2,
	BoxIntro:     2,
	BoxElim:      2,
	DiamondIntro: 1,
	DiamondElim:  3,
	IntroD:       1,
	IntroM:       1,
	ElimM:        1,
	Intro4:       1,
	Elim4:        1,
	IntroB:       1,
	ElimB:        1,
}

func correctJCount(rule, purp NDRule, lenJ int) (ok bool) {
	var (
		lenC int
	)

	if rule == Assumption {
		if lenC, ok = purposePCount[purp]; ok {
			ok = lenJ == lenC
		}
	} else if lenC, ok = rulePCount[rule]; ok {
		ok = lenJ == lenC
	}

	return
}
