package pr

import "strings"

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
	SystemD
	SystemM
	System4
	SystemB
	// Extensions from K:
	SystemKD
	SystemKM
	SystemK4
	SystemKB
	// Extensions from D:
	SystemDM
	SystemD4
	SystemDB
	// Extensions from M:
	SystemM4
	SystemMB
	// Extensions from KD:
	SystemKDM
	SystemKD4
	SystemKDB
	// Extensions from KM:
	SystemKM4
	SystemKMB
	// Extensions from K4:
	SystemK4B
	// Extensions from DM:
	SystemDM4
	SystemDMB
	// Extensions from D4:
	SystemD4B
	// Extensions from M4:
	SystemM4B
	// Extensions from KDM:
	SystemKDM4
	SystemKDMB
	// Extensions from KD4:
	SystemKD4B
	// Extensions from KM4:
	SystemKM4B
	// Extensions from DM4:
	SystemDM4B
	// Extensions from KDM4:
	SystemKDM4B
)

var modalSystemToString map[ModStrength]string = map[ModStrength]string{
	NoSystem: "NoSystem",
	SystemK:  "K",
	SystemD:  "D",
	SystemM:  "M",
	System4:  "4",
	SystemB:  "B",
	// Extensions from K:
	SystemKD: "KD",
	SystemKM: "KM",
	SystemK4: "K4",
	SystemKB: "KB",
	// Extensions from D:
	SystemDM: "DM",
	SystemD4: "D4",
	SystemDB: "DB",
	// Extensions from M:
	SystemM4: "M4",
	SystemMB: "MB",
	// Extensions from KD:
	SystemKDM: "KDM",
	SystemKD4: "KD4",
	SystemKDB: "KDB",
	// Extensions from KM:
	SystemKM4: "KM4",
	SystemKMB: "KMB",
	// Extensions from K4:
	SystemK4B: "K4B",
	// Extensions from DM:
	SystemDM4: "DM4",
	SystemDMB: "DMB",
	// Extensions from D4:
	SystemD4B: "D4B",
	// Extensions from M4:
	SystemM4B: "M4B",
	// Extensions from KDM:
	SystemKDM4: "KDM4",
	SystemKDMB: "KDMB",
	// Extensions from KD4:
	SystemKD4B: "KD4B",
	// Extensions from KM4:
	SystemKM4B: "KM4B",
	// Extensions from DM4:
	SystemDM4B: "DM4B",
	// Extensions from KDM4:
	SystemKDM4B: "KDM4B",
}

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

func minimalModalStrengthOfNDRule(rule NDRule) (modM ModStrength) {
	var infS InfStrength

	switch rule {
	case BoxIntro, BoxElim, DiamondElim, DiamondIntro:
		modM = NoSystem
	case IntroK:
		modM = SystemK
	case ElimD:
		modM = SystemD
	case IntroM, ElimM:
		modM = SystemM
	case Intro4, Elim4:
		modM = System4
	case IntroB, ElimB:
		modM = SystemB
	default:
		if infS = inferStrengthOfNDRule(rule); !(infS < NoInference) {
			modM = NoSystem
		}
	}

	return
}

func IsAllowedModality(rule NDRule, modS ModStrength) (is bool) {
	var (
		modM   ModStrength
		sM, sS string
	)

	if modM = minimalModalStrengthOfNDRule(rule); modM == NoSystem {
		is = true
	} else {
		sM, sS = modalSystemToString[modM], modalSystemToString[modS]

		is = strings.Contains(sS, sM)
	}

	return
}
