package pr

type NDRule uint8

// Note: DO NOT adjust the order of these rules,
// as they will play a part in determining the kind of logic
// that is needed to derive a given theorem.
const (
	// Assumpions
	Assumption NDRule = iota + 1
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

var purposes = []NDRule{
	ToIntro, NegIntro,
	ForAllIntro, ExistsElim,
	BoxIntro, DiamondElim,
}
