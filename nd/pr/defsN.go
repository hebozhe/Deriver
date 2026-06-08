package pr

import (
	"Deriver/fmla"
)

type ndRuleFunc func(prf *Proof) (added uint)

type SynBreadth uint
type InfStrength uint
type ModStrength uint

const (
	bL SynBreadth = 1  // Base
	PL SynBreadth = 2  // Propositional Logic
	NL SynBreadth = 3  // N-ary Predicate Logic
	I  SynBreadth = 5  // Identity Predicate
	QL SynBreadth = 7  // Quantificational Logic
	ML SynBreadth = 11 // Modal Logic
)

func GetSyntacticBreadth(wffs ...*fmla.Wff) (synB SynBreadth) {
	var (
		wff        *fmla.Wff
		mop        fmla.Symbol
		pred       fmla.Predicate
		args       []fmla.Argument
		lenA       int
		ok         bool
		subL, subR *fmla.Wff
	)

	synB = bL

	for _, wff = range wffs {
		mop = fmla.GetWffMop(wff)

		switch mop {
		case fmla.NoSymbol:
			if pred, args, ok = fmla.GetWffPredAndArgs(wff); ok {
				synB = synB * PL

				if pred == fmla.Equals {
					synB = synB * NL * I
				}

				if lenA = len(args); 0 < lenA {
					synB = synB * NL
				}
			}
		case fmla.Neg:
			subL, _ = fmla.GetWffSubformulae(wff)

			synB = synB * PL * GetSyntacticBreadth(subL)
		case fmla.Wedge, fmla.Vee, fmla.To, fmla.Iff:
			subL, subR = fmla.GetWffSubformulae(wff)

			synB = synB * PL * GetSyntacticBreadth(subL, subR)
		case fmla.Exists, fmla.ForAll:
			subL, _ = fmla.GetWffSubformulae(wff)

			synB = synB * QL * GetSyntacticBreadth(subL)
		case fmla.Box, fmla.Diamond:
			subL, _ = fmla.GetWffSubformulae(wff)

			synB = synB * ML * GetSyntacticBreadth(subL)
		default:
			panic("Cannot determine syntactic breadth.")
		}

		// Reduce the syntactic breadth for every formula.
		for synB%(PL*PL) == 0 {
			synB = synB / PL
		}

		for synB%(NL*NL) == 0 {
			synB = synB / NL
		}

		for synB%(I*I) == 0 {
			synB = synB / I
		}

		for synB%(QL*QL) == 0 {
			synB = synB / QL
		}

		for synB%(ML*ML) == 0 {
			synB = synB / ML
		}
	}

	return
}

func IsRuleForSyntacticBreadth(rule NDRule, synB SynBreadth) (is bool) {
	switch rule {
	// case Solve, Premise, Theorem, Assumption:
	// 	is = false
	case TopIntro, ToIntro, ToElim, Reiteration,
		WedgeIntro, WedgeElim, VeeIntro, VeeElim, IffIntro, IffElim,
		BotIntro, BotElim, NegIntro, NegElim:
		is = synB%PL == 0 || synB%NL == 0
	case ForAllIntro, ForAllElim, ExistsIntro, ExistsElim:
		is = synB%QL == 0
	case EqualsIntro, EqualsElim:
		is = synB%NL == 0 && synB%I == 0
	case BoxIntro, BoxElimC, BoxElimW, DiamondElim, DiamondIntro,
		ElimD, IntroM, ElimM, Intro4, Elim4, IntroB, ElimB:
		is = synB%ML == 0
	}

	return
}

const (
	NoInference InfStrength = iota
	Implicational
	Positive
	Minimal
	Intuitionistic
	Classical
)

func inferentialStrengthOfNDRule(rule NDRule) (infS InfStrength) {
	switch rule {
	case Solve, Premise, Assumption:
		infS = NoInference
	case TopIntro, Reiteration,
		ToIntro, ToElim,
		EqualsIntro, EqualsElim:
		infS = Implicational
	case WedgeIntro, WedgeElim, VeeIntro, VeeElim, IffIntro, IffElim, BoxIntro, BoxElimC, DiamondElim:
		infS = Positive
	case BotIntro, NegIntro, BoxElimW:
		infS = Minimal
	case BotElim:
		infS = Intuitionistic
	case NegElim, DiamondIntro:
		infS = Classical
	case ForAllIntro, ForAllElim,
		ExistsIntro, ExistsElim:
		infS = Positive
	case ElimD, IntroM, ElimM, Intro4, Elim4, IntroB, ElimB:
		infS = Positive
	default:
		panic("Failed to capture NDRule.")
	}

	return
}

func modalStrengthOfNDRule(rule NDRule) (modS ModStrength) {
	switch rule {
	case BoxIntro, BoxElimC, DiamondElim, DiamondIntro:
		modS = ModalK
	case ElimD:
		modS = ModalD
	case ElimM, IntroM:
		modS = ModalM
	case Elim4, Intro4:
		modS = Modal4
	case ElimB, IntroB:
		modS = ModalB
	default:
		modS = NoModality
	}

	return
}

const (
	NoModality ModStrength = 1
	ModalK     ModStrength = 2
	ModalD     ModStrength = 3
	ModalM     ModStrength = 5
	Modal4     ModStrength = 7
	ModalB     ModStrength = 11
	// Extensions from K:
	ModalKD ModStrength = ModalK * ModalD
	ModalKM ModStrength = ModalK * ModalM
	ModalK4 ModStrength = ModalK * Modal4
	ModalKB ModStrength = ModalK * ModalB
	// Extensions from D:
	ModalDM ModStrength = ModalD * ModalM
	ModalD4 ModStrength = ModalD * Modal4
	ModalDB ModStrength = ModalD * ModalB
	// Extensions from M:
	ModalM4 ModStrength = ModalM * Modal4
	ModalMB ModStrength = ModalM * ModalB
	// Extensions from 4:
	Modal4B ModStrength = Modal4 * ModalB
	// Extensions from KD:
	ModalKDM ModStrength = ModalKD * ModalM
	ModalKD4 ModStrength = ModalKD * Modal4
	ModalKDB ModStrength = ModalKD * ModalB
	// Extensions from KM:
	ModalKM4 ModStrength = ModalKM * Modal4
	ModalKMB ModStrength = ModalKM * ModalB
	// Extensions from K4:
	ModalK4B ModStrength = ModalK4 * ModalB
	// Extensions from DM:
	ModalDM4 ModStrength = ModalDM * Modal4
	ModalDMB ModStrength = ModalDM * ModalB
	// Extensions from D4:
	ModalD4B ModStrength = ModalD4 * ModalB
	// Extensions from M4:
	ModalM4B ModStrength = ModalM4 * ModalB
	// Extensions from KDM:
	ModalKDM4 ModStrength = ModalKDM * Modal4
	ModalKDMB ModStrength = ModalKDM * ModalB
	// Extensions from KD4:
	ModalKD4B ModStrength = ModalKD4 * ModalB
	// Extensions from KM4:
	ModalKM4B ModStrength = ModalKM4 * ModalB
	// Extensions from DM4:
	ModalDM4B ModStrength = ModalDM4 * ModalB
	// Extensions from KDM4:
	ModalKDM4B ModStrength = ModalKDM4 * ModalB
)

func GetInferentialStrengthOfNDRules(rules ...NDRule) (infS InfStrength) {
	var (
		rule  NDRule
		infSX InfStrength
	)

	infS = NoInference

	for _, rule = range rules {
		if infSX = inferentialStrengthOfNDRule(rule); infS < infSX {
			infS = infSX
		}

		if infS == Classical {
			break
		}
	}

	return
}

func GetModalStrengthOfNDRules(rules ...NDRule) (modS ModStrength) {
	var (
		rule  NDRule
		modSX ModStrength
	)

	modS = NoModality

	for _, rule = range rules {
		if modSX = modalStrengthOfNDRule(rule); modS%modSX != 0 {
			modS = modS * modSX
		}

		if modS == ModalKDM4B {
			break
		}
	}

	return
}

func HasModality(modSA ModStrength, modSB ModStrength) (has bool) {
	has = modSA%modSB == 0

	return
}

func CountModalities(modS ModStrength) (n int) {
	switch {
	case modS == NoModality:
		n = 0
	case modS%ModalK == 0:
		n = 1 + CountModalities(modS/ModalK)
	case modS%ModalD == 0:
		n = 1 + CountModalities(modS/ModalD)
	case modS%ModalM == 0:
		n = 1 + CountModalities(modS/ModalM)
	case modS%Modal4 == 0:
		n = 1 + CountModalities(modS/Modal4)
	case modS%ModalB == 0:
		n = 1 + CountModalities(modS/ModalB)
	default:
		panic("Modality not handled.")
	}

	return
}
