package pr

import (
	"slices"
)

type ndRuleFunc func(prf *Proof) (added uint)

type InfStrength uint
type ModStrength uint

const (
	NoInference InfStrength = iota
	Implicational
	Positive
	Minimal
	Intuitionistic
	Classical
)

const (
	NoSystem ModStrength = iota
	SystemK
	SystemKD
	SystemK4
	SystemKB
	SystemKM // Proves all that KDM does.
	SystemKD4
	SystemKDB
	SystemK4B
	SystemKM4  // Proves all that KDM4 does.
	SystemKMB  // Proves all that KDMB does.
	SystemKM4B // Proves all the KD4B and KDM4B does.
)

func inferStrengthOfNDRule(rule NDRule) (infS InfStrength) {
	switch rule {
	case Solve, Premise, Theorem, Assumption:
		infS = NoInference
	case TopIntro, Reiteration,
		ToIntro, ToElim,
		EqualsIntro, EqualsElim:
		infS = Implicational
	case WedgeIntro, WedgeElim, VeeIntro, VeeElim, IffIntro, IffElim, BoxIntro, BoxElim, DiamondElim:
		infS = Positive
	case BotIntro, NegIntro:
		infS = Minimal
	case BotElim:
		infS = Intuitionistic
	case NegElim, DiamondIntro:
		infS = Classical
	case ForAllIntro, ForAllElim,
		ExistsIntro, ExistsElim:
		infS = Positive
	case IntroK, ElimD, IntroM, ElimM,
		Intro4, Elim4, IntroB, ElimB:
		infS = Positive
	default:
		panic("Failed to capture NDRule.")
	}

	return
}

func InferStrengthOfNDRules(rules ...NDRule) (infS InfStrength) {
	var (
		rule  NDRule
		infSX InfStrength
	)

	for _, rule = range rules {
		if infSX = inferStrengthOfNDRule(rule); infS < infSX {
			infS = infSX
		}

		if infS == Classical {
			break
		}
	}

	return
}

func modalStrengthOfNDRule(rule NDRule) (modS ModStrength) {
	var infS InfStrength

	switch rule {
	case BoxIntro, BoxElim, DiamondElim, DiamondIntro:
		modS = NoSystem
	case IntroK:
		modS = SystemK
	case ElimD:
		modS = SystemKD
	case IntroM, ElimM:
		modS = SystemKM
	case Intro4, Elim4:
		modS = SystemK4
	case IntroB, ElimB:
		modS = SystemKB
	default:
		if infS = inferStrengthOfNDRule(rule); !(infS < NoInference) {
			modS = NoSystem
		}
	}

	return
}

func ModalStrengthOfNDRules(rules ...NDRule) (modS ModStrength) {
	var (
		ruleToModS map[string]ModStrength
		rule       NDRule
		key        []string
		s          string
	)

	ruleToModS = map[string]ModStrength{
		"":      NoSystem,
		"K":     SystemK,
		"KD":    SystemKD,
		"K4":    SystemK4,
		"KB":    SystemKB,
		"KDM":   SystemKM,
		"KD4":   SystemKD4,
		"KDB":   SystemKDB,
		"K4B":   SystemK4B,
		"KDM4":  SystemKM4,
		"KDMB":  SystemKMB,
		"KDM4B": SystemKM4B,
	}

	for _, rule = range rules {
		if modS = modalStrengthOfNDRule(rule); modS == NoSystem {
			continue
		}

		switch modS {
		case SystemK:
			key = append(key, "K")
		case SystemKD:
			key = append(key, "K", "D")
		case SystemK4:
			key = append(key, "K", "4")
		case SystemKB:
			key = append(key, "K", "B")
		case SystemKM:
			key = append(key, "K", "D", "M")
		case SystemKD4:
			key = append(key, "K", "D", "4")
		case SystemKDB:
			key = append(key, "K", "D", "B")
		case SystemK4B:
			key = append(key, "K", "4", "B")
		case SystemKM4:
			key = append(key, "K", "D", "M", "4")
		case SystemKMB:
			key = append(key, "K", "D", "M", "B")
		case SystemKM4B:
			key = append(key, "K", "D", "M", "4", "B")
		default:
			panic("Failed to capture NDRule.")
		}
	}

	s = ""

	if slices.Contains(key, "K") {
		s += "K"
	}

	if slices.Contains(key, "D") {
		s += "D"
	}

	if slices.Contains(key, "M") {
		s += "M"
	}

	if slices.Contains(key, "4") {
		s += "4"
	}

	if slices.Contains(key, "B") {
		s += "B"
	}

	modS = ruleToModS[s]

	return
}

func IsAllowedModality(rule NDRule, modS ModStrength) (is bool) {
	var (
		modR        ModStrength
		modSToAllow map[ModStrength][]NDRule
	)

	if modR = modalStrengthOfNDRule(rule); modR == NoSystem {
		is = true
	} else {
		modSToAllow = map[ModStrength][]NDRule{}

		modSToAllow[SystemK] = []NDRule{IntroK}

		modSToAllow[SystemKD] = append([]NDRule{}, modSToAllow[SystemK]...)
		modSToAllow[SystemKD] = append(modSToAllow[SystemKD], ElimD)

		modSToAllow[SystemK4] = append([]NDRule{}, modSToAllow[SystemK]...)
		modSToAllow[SystemK4] = append(modSToAllow[SystemK4], Intro4, Elim4)

		modSToAllow[SystemKB] = append([]NDRule{}, modSToAllow[SystemK]...)
		modSToAllow[SystemKB] = append(modSToAllow[SystemKB], IntroB, ElimB)

		modSToAllow[SystemKM] = append([]NDRule{}, modSToAllow[SystemKD]...)
		modSToAllow[SystemKM] = append(modSToAllow[SystemKM], IntroM, ElimM)

		modSToAllow[SystemKD4] = append([]NDRule{}, modSToAllow[SystemKD]...)
		modSToAllow[SystemKD4] = append(modSToAllow[SystemKD4], Intro4, Elim4)

		modSToAllow[SystemKDB] = append([]NDRule{}, modSToAllow[SystemKD]...)
		modSToAllow[SystemKDB] = append(modSToAllow[SystemKDB], IntroB, ElimB)

		modSToAllow[SystemK4B] = append([]NDRule{}, modSToAllow[SystemK4]...)
		modSToAllow[SystemK4B] = append(modSToAllow[SystemK4B], IntroB, ElimB)

		modSToAllow[SystemKM4] = append([]NDRule{}, modSToAllow[SystemKM]...)
		modSToAllow[SystemKM4] = append(modSToAllow[SystemKM4], Intro4, Elim4)

		modSToAllow[SystemKMB] = append([]NDRule{}, modSToAllow[SystemKM]...)
		modSToAllow[SystemKMB] = append(modSToAllow[SystemKMB], IntroB, ElimB)

		modSToAllow[SystemKM4B] = append([]NDRule{}, modSToAllow[SystemKM4]...)
		modSToAllow[SystemKM4B] = append(modSToAllow[SystemKM4B], IntroB, ElimB)

		is = slices.Contains(modSToAllow[modS], rule)
	}

	return
}
