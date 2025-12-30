package nd

import (
	"Deriver/nd/pr"
)

type ndRuleFunc func(prf *pr.Proof) (added uint)

type InferStrength uint
type ModalStrength uint

const (
	Implicational InferStrength = iota + 1
	Positive
	Minimal
	Intuitionistic
	Classical
)

const (
	SystemK ModalStrength = iota + 1
	SystemKD
	SystemK4
	SystemKB
	SystemKM // Proves all that KDM does.
	SystemKD4
	SystemKDB
	SystemK4B
	SystemKM4  // Proves all that KDM4 does.
	SystemKMB  // Proves all that KDMB does.
	SystemKD4B // Proves all the KM4B and KDM4B does.
)

var rulesToFuncs map[pr.NDRule]ndRuleFunc = map[pr.NDRule]ndRuleFunc{
	pr.TopIntro:     tryTopIntro,
	pr.ToIntro:      tryToIntro,
	pr.ToElim:       tryToElim,
	pr.WedgeIntro:   tryWedgeIntro,
	pr.WedgeElim:    tryWedgeElim,
	pr.VeeIntro:     tryVeeIntro,
	pr.VeeElim:      tryVeeElim,
	pr.IffIntro:     tryIffIntro,
	pr.IffElim:      tryIffElim,
	pr.Reit:         tryReit,
	pr.BotIntro:     tryBotIntro,
	pr.BotElim:      tryBotElim,
	pr.NegIntro:     tryNegIntro,
	pr.NegElim:      tryNegElim,
	pr.ForAllIntro:  tryForAllIntro,
	pr.ForAllElim:   tryForAllElim,
	pr.ExistsIntro:  tryExistsIntro,
	pr.ExistsElim:   tryExistsElim,
	pr.EqualsIntro:  tryEqualsIntro,
	pr.EqualsElim:   tryEqualsElim,
	pr.BoxIntro:     tryBoxIntro,
	pr.BoxElim:      tryBoxElim,
	pr.DiamondIntro: tryDiamondIntro,
	pr.DiamondElim:  tryDiamondElim,
	pr.IntroD:       tryIntroD,
	pr.IntroM:       tryIntroM,
	pr.ElimM:        tryElimM,
	pr.Intro4:       tryIntro4,
	pr.Elim4:        tryElim4,
	pr.IntroB:       tryIntroB,
	pr.ElimB:        tryElimB,
}

func rulesInInferStrength(infS InferStrength) (iRules, eRules []pr.NDRule) {
	switch infS {
	case Implicational:
		iRules = []pr.NDRule{pr.TopIntro, pr.ToIntro}

		eRules = []pr.NDRule{pr.ToElim}
	case Positive:
		iRules, eRules = rulesInInferStrength(Implicational)

		iRules = append(iRules, pr.WedgeIntro, pr.VeeIntro, pr.IffIntro, pr.Reit)

		eRules = append(eRules, pr.WedgeElim, pr.VeeElim, pr.IffElim)
	case Minimal:
		iRules, eRules = rulesInInferStrength(Positive)

		iRules = append(iRules, pr.BotIntro, pr.NegIntro)
	case Intuitionistic:
		iRules, eRules = rulesInInferStrength(Minimal)

		eRules = append(eRules, pr.BotElim)
	case Classical:
		iRules, eRules = rulesInInferStrength(Intuitionistic)

		eRules = append(eRules, pr.NegElim)
	default:
		panic("Invalid InferStrength")
	}

	iRules = append(iRules, pr.ForAllIntro, pr.ExistsIntro, pr.EqualsIntro)

	eRules = append(eRules, pr.ForAllElim, pr.ExistsElim, pr.EqualsElim)

	return
}

func rulesInModalStrength(modS ModalStrength, infS InferStrength) (iRules, eRules []pr.NDRule) {
	switch modS {
	case SystemK:
		iRules = []pr.NDRule{pr.BoxIntro}

		eRules = []pr.NDRule{pr.BoxElim, pr.DiamondElim}

		if infS == Classical {
			iRules = append(iRules, pr.DiamondIntro)
		}
	case SystemKD:
		iRules, eRules = rulesInModalStrength(SystemK, infS)

		iRules = append(iRules, pr.IntroD)
	case SystemK4:
		iRules, eRules = rulesInModalStrength(SystemK, infS)

		iRules = append(iRules, pr.Intro4)

		eRules = append(eRules, pr.Elim4)
	case SystemKB:
		iRules, eRules = rulesInModalStrength(SystemK, infS)

		iRules = append(iRules, pr.IntroB)

		eRules = append(eRules, pr.ElimB)
	case SystemKM:
		iRules, eRules = rulesInModalStrength(SystemKD, infS)

		iRules = append(iRules, pr.IntroM)

		eRules = append(eRules, pr.ElimM)
	case SystemKD4:
		iRules, eRules = rulesInModalStrength(SystemKD, infS)

		iRules = append(iRules, pr.Intro4)

		eRules = append(eRules, pr.Elim4)
	case SystemKDB:
		iRules, eRules = rulesInModalStrength(SystemKD, infS)

		iRules = append(iRules, pr.IntroB)

		eRules = append(eRules, pr.ElimB)
	case SystemK4B:
		iRules, eRules = rulesInModalStrength(SystemK4, infS)

		iRules = append(iRules, pr.IntroB)

		eRules = append(eRules, pr.ElimB)
	case SystemKM4:
		iRules, eRules = rulesInModalStrength(SystemKM, infS)

		iRules = append(iRules, pr.Intro4)

		eRules = append(eRules, pr.Elim4)
	case SystemKMB:
		iRules, eRules = rulesInModalStrength(SystemKM, infS)

		iRules = append(iRules, pr.IntroB)

		eRules = append(eRules, pr.ElimB)
	case SystemKD4B:
		iRules, eRules = rulesInModalStrength(SystemKD4, infS)

		iRules = append(iRules, pr.IntroB)

		eRules = append(eRules, pr.ElimB)
	default:
		panic("Invalid ModalStrength")
	}

	return
}

func incInferStrength(infS InferStrength) (incInfS InferStrength) {
	incInfS = min(infS+1, Classical)

	return
}

func incModalStrength(modS ModalStrength) (incModS ModalStrength) {
	incModS = min(modS+1, SystemKD4B)

	return
}

func ruleFuncsByStrengths(infS InferStrength, modS ModalStrength) (iFuncs, eFuncs []ndRuleFunc) {
	var (
		iRulesPQ, eRulesPQ, iRulesM, eRulesM []pr.NDRule
		rule                                 pr.NDRule
	)

	iRulesPQ, eRulesPQ = rulesInInferStrength(infS)

	iRulesM, eRulesM = rulesInModalStrength(modS, infS)

	for _, rule = range iRulesPQ {
		iFuncs = append(iFuncs, rulesToFuncs[rule])
	}

	for _, rule = range eRulesPQ {
		eFuncs = append(eFuncs, rulesToFuncs[rule])
	}

	for _, rule = range iRulesM {
		iFuncs = append(iFuncs, rulesToFuncs[rule])
	}

	for _, rule = range eRulesM {
		eFuncs = append(eFuncs, rulesToFuncs[rule])
	}

	return
}
