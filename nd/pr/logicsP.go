package pr

import (
	"Deriver/fmla"
	"Deriver/gen"
	"fmt"
	"strings"
	"unicode/utf8"
)

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

func simplifySynBreadth(syn SynBreadth) (synS SynBreadth) {
	synS = bL

	if syn%PL == 0 {
		synS *= PL
	}

	if syn%NL == 0 {
		synS *= NL
	}

	if syn%I == 0 {
		synS *= I
	}

	if syn%QL == 0 {
		synS *= QL
	}

	if syn%ML == 0 {
		synS *= ML
	}

	return
}

func synBreadthOfWff(wff *fmla.Wff) (syn SynBreadth) {
	var (
		subL, subR *fmla.Wff
		arity      int
	)

	syn = bL

	subL, subR, arity = wff.Subs()

	switch arity {
	case 0: // Atomic.
		if wff.Pred() != fmla.NoPred {
			syn *= PL
		}

		if 0 < wff.Valency() {
			syn *= NL
		}

		if wff.Pred() == fmla.Equal {
			syn *= I
		}
	case 1: // Unary or Quantified.
		switch wff.Mop() {
		case fmla.Neg:
			syn *= PL * SynBreadthOfWffs(subL)
		case fmla.ForAll, fmla.Exists:
			syn *= QL * SynBreadthOfWffs(subL)
		case fmla.Box, fmla.Dmd:
			syn *= ML * SynBreadthOfWffs(subL)
		}
	case 2: // Binary.
		syn *= PL * SynBreadthOfWffs(subL) * SynBreadthOfWffs(subR)
	}

	syn = simplifySynBreadth(syn)

	return
}

func SynBreadthOfWffs(wffs ...*fmla.Wff) (syn SynBreadth) {
	var (
		wff *fmla.Wff
	)

	syn = bL

	for _, wff = range wffs {
		syn *= synBreadthOfWff(wff)
	}

	syn = simplifySynBreadth(syn)

	return
}

func RuleFitsSynBreadth(rule NDRule, syn SynBreadth) (fits bool) {
	switch rule {
	case Solve, Prem, Ass:
		fits = true
	case TopI, ToI, ToE, Reit, Thm, WedgeI, WedgeE, VeeI, VeeE, IffI, IffE, BotI, BotE, NegI, NegE, Jan, Göd, Sme:
		fits = syn%PL == 0
	case EqualI, EqualE:
		fits = syn%(NL*I) == 0
	case ForAllI, ForAllE, ExistsI, ExistsE:
		fits = syn%QL == 0
	case BoxCon, DmdCon, BoxIntEw, DmdIntEw, BoxIntEn, DmdIntEn, BoxIntEs, DmdIntEs, DmdI,
		BoxMon, DmdMon, BoxE, DmdE, BoxI, NegDmdI, BoxAgg, ReitC, ReitK,
		RuleD, IntroT, ElimT, Intro4, Elim4, IntroB, ElimB, Intro5, Elim5:
		fits = syn%ML == 0
	default:
		panic(fmt.Sprintf("Unrecognized rule: %d", rule))
	}

	return
}

const (
	NoInference InfStrength = iota
	Implicational
	Positive
	Minimal
	Intuitionistic
	Jankov // KC
	GödelDummett
	Smetanich
	Classical
)

const (
	NoModality ModStrength = 1
	// Non-normal modal logics.
	ModalEw ModStrength = 2
	ModalEn ModStrength = 3
	ModalEs ModStrength = 5
	ModalM  ModStrength = 7
	ModalN  ModStrength = 11
	ModalC  ModStrength = 13
	// Normal modal logic.
	ModalK ModStrength = 17
	// Modal logic extensions.
	ModalD ModStrength = 19
	ModalT ModStrength = 23
	Modal4 ModStrength = 29
	ModalB ModStrength = 31
	Modal5 ModStrength = 37
)

func HasAnyModality(modA ModStrength, modsB ...ModStrength) (has bool) {
	var (
		modB ModStrength
	)

	for _, modB = range modsB {
		if has = modA%modB == 0; has {
			break
		}
	}

	return
}

func RuleFitsStrengths(rule NDRule, inf InfStrength, mod ModStrength) (fits bool) {
	switch rule {
	case Solve, Prem, Ass:
		fits = !(inf < NoInference)
	case TopI, ToI, ToE, Reit, Thm:
		fits = NoInference < inf
	case WedgeI, WedgeE, VeeI, VeeE, IffI, IffE:
		fits = Implicational < inf
	case BotI, NegI:
		fits = Positive < inf
	case BotE:
		fits = Minimal < inf
	case Jan:
		fits = Intuitionistic < inf
	case Göd:
		fits = Jankov < inf
	case Sme:
		fits = GödelDummett < inf
	case NegE:
		fits = Smetanich < inf
	case EqualI, EqualE:
		fits = NoInference < inf
	case ForAllI, ForAllE, ExistsI, ExistsE:
		fits = Implicational < inf
	case BoxCon, DmdCon:
		fits = Implicational < inf && HasAnyModality(mod, ModalEw, ModalEn, ModalEs, ModalM, ModalK)
	case BoxIntEw, DmdIntEw:
		fits = Positive < inf && HasAnyModality(mod, ModalEw, ModalEn, ModalEs, ModalM, ModalK)
	case BoxIntEn:
		fits = Positive < inf && HasAnyModality(mod, ModalEn, ModalEs, ModalM, ModalK)
	case DmdIntEn:
		fits = Positive < inf && HasAnyModality(mod, ModalEs, ModalM, ModalK)
		fits = fits || (Positive < inf && mod%ModalEn == 0 && mod%(ModalEn*ModalC) != 0)
	case BoxIntEs, DmdIntEs:
		fits = Positive < inf && HasAnyModality(mod, ModalEs, ModalM, ModalK)
	case DmdI:
		fits = Smetanich < inf && HasAnyModality(mod, ModalEw, ModalEn, ModalEs, ModalM, ModalN, ModalC, ModalK)
	case BoxMon, DmdMon, BoxE, DmdE:
		fits = Implicational < inf && HasAnyModality(mod, ModalM, ModalK)
	case BoxI:
		fits = Implicational < inf && HasAnyModality(mod, ModalN, ModalK)
	case NegDmdI:
		fits = Positive < inf && HasAnyModality(mod, ModalN, ModalK)
	case BoxAgg:
		fits = Implicational < inf && HasAnyModality(mod, ModalC, ModalK)
	case ReitC:
		fits = Implicational < inf && HasAnyModality(mod, ModalC*ModalM, ModalC*ModalN, ModalK)
	case ReitK:
		fits = Implicational < inf && mod%ModalK == 0
	case RuleD:
		fits = Implicational < inf && mod%ModalD == 0
	case IntroT, ElimT:
		fits = Implicational < inf && mod%ModalT == 0
	case Intro4, Elim4:
		fits = Implicational < inf && mod%Modal4 == 0
	case IntroB, ElimB:
		fits = Implicational < inf && mod%ModalB == 0
	case Intro5, Elim5:
		fits = Implicational < inf && mod%Modal5 == 0
	default:
		panic("Unrecognized rule.")
	}

	return
}

func NameLogic(inf InfStrength, syn SynBreadth, mod ModStrength) (name string) {
	switch inf {
	case Implicational:
		name += "T"
	case Positive:
		name += "P"
	case Minimal:
		name += "M"
	case Intuitionistic:
		name += "I"
	case Jankov:
		name += "J"
	case GödelDummett:
		name += "G"
	case Smetanich:
		name += "S"
	case Classical:
		name += "C"
	}

	switch {
	case syn%QL == 0:
		name += "QL"
	case syn%NL == 0:
		name += "NL"
	case syn%PL == 0:
		name += "PL"
	}

	if syn%I == 0 {
		name += "i"
	}

	if syn%ML == 0 {
		name += "+"

		if mod%ModalK == 0 { // The logic is normal.
			name += "K"
		} else {
			// Scale from monotonicity to weaker congruencies.
			switch {
			case mod%ModalM == 0:
				name += "M"
			case mod%ModalEs == 0:
				name += "Es"
			case mod%ModalEn == 0:
				name += "En"
			case mod%ModalEw == 0:
				name += "Ew"
			}

			if mod%ModalC == 0 {
				name += "C"
			}

			if mod%ModalN == 0 {
				name += "N"
			}
		}

		if mod%ModalD == 0 {
			name += "D"
		}

		if mod%ModalT == 0 {
			name += "T"
		}

		if mod%Modal4 == 0 {
			name += "4"
		}

		if mod%ModalB == 0 {
			name += "B"
		}

		if mod%Modal5 == 0 {
			name += "5"
		}
	}

	return
}

func ExtractLogic(name string) (inf InfStrength, syn SynBreadth, mod ModStrength) {
	var (
		lenN int
	)

	if name == "" {
		panic("Incomplete logic name.")
	}

	switch name[0] {
	case 'T':
		inf = Implicational
	case 'P':
		inf = Positive
	case 'M':
		inf = Minimal
	case 'I':
		inf = Intuitionistic
	case 'J':
		inf = Jankov
	case 'G':
		inf = GödelDummett
	case 'S':
		inf = Smetanich
	case 'C':
		inf = Classical
	default:
		panic("Unrecognized inferential strength.")
	}

	name = name[1:]

	if lenN = utf8.RuneCountInString(name); lenN < 2 || name[1] != 'L' {
		panic("Missing syntactic breadth.")
	}

	switch name[0:2] {
	case "QL":
		syn = PL * NL * QL
	case "NL":
		syn = PL * NL
	case "PL":
		syn = PL
	default:
		panic("Unrecognized syntactic breadth.")
	}

	name = name[2:]

	if lenN = utf8.RuneCountInString(name); 0 < lenN && name[0] == 'i' {
		syn *= I

		name = name[1:]
	}

	mod = NoModality

	if lenN = utf8.RuneCountInString(name); 1 < lenN && name[0] == '+' {
		syn *= ML

		name = name[1:]

		for name != "" {
			switch {
			case name[0] == 'E':
				if lenN = utf8.RuneCountInString(name); 1 < lenN {
					switch name[1] {
					case 'w':
						mod, name = mod*ModalEw, name[2:]
					case 'n':
						mod, name = mod*ModalEn, name[2:]
					case 's':
						mod, name = mod*ModalEs, name[2:]
					default:
						panic("Unrecognized modality.")
					}
				} else {
					panic("Unrecognized modality.")
				}
			case name[0] == 'M':
				mod, name = mod*ModalM, name[1:]
			case name[0] == 'C':
				mod, name = mod*ModalC, name[1:]
			case name[0] == 'N':
				mod, name = mod*ModalN, name[1:]
			case name[0] == 'K':
				mod, name = mod*ModalK, name[1:]
			case name[0] == 'D':
				mod, name = mod*ModalD, name[1:]
			case name[0] == 'T':
				mod, name = mod*ModalT, name[1:]
			case name[0] == '4':
				mod, name = mod*Modal4, name[1:]
			case name[0] == 'B':
				mod, name = mod*ModalB, name[1:]
			case name[0] == '5':
				mod, name = mod*Modal5, name[1:]
			default:
				panic("Unrecognized modality.")
			}
		}
	}

	if name != "" {
		panic("Unrecognized logic.")
	}

	return
}

func StrongestLogic(syn SynBreadth) (name string) {
	if syn%ML == 0 {
		name += NameLogic(Classical, syn, ModalK*ModalD*ModalT*Modal4*ModalB*Modal5)
	} else {
		name = NameLogic(Classical, syn, NoModality)
	}

	return
}

func WeakenLogic(name string) (weakened []string) {
	var (
		inf                    InfStrength
		mod                    ModStrength
		infSeg, modSeg, weaker string
	)

	inf, _, mod = ExtractLogic(name)

	// Step down inferential strength (first character of name).
	switch inf {
	case Classical:
		weakened = append(weakened, "S"+name[1:])
	case Smetanich:
		weakened = append(weakened, "G"+name[1:])
	case GödelDummett:
		weakened = append(weakened, "J"+name[1:])
	case Jankov:
		weakened = append(weakened, "I"+name[1:])
	case Intuitionistic:
		weakened = append(weakened, "M"+name[1:])
	case Minimal:
		weakened = append(weakened, "P"+name[1:])
	case Positive:
		weakened = append(weakened, "T"+name[1:])
	case Implicational:
		weakened = []string{}
	default:
		panic("Unrecognized inferential strength.")
	}

	// Step down the identity predicate.
	if strings.ContainsRune(name, 'i') {
		weaker = strings.Replace(name, "i", "", 1)

		weakened = append(weakened, weaker)
	}

	// Step down modalities.
	if mod != NoModality {
		infSeg, modSeg, _ = strings.Cut(name, "+")

		// Step down the linear modal chain: K -> MCN and M -> Es -> En -> Ew -> (none).
		switch {
		case mod%ModalK == 0:
			weaker = infSeg + "+" + strings.Replace(modSeg, "K", "MCN", 1)

			weakened = append(weakened, weaker)
		case mod%ModalM == 0:
			weaker = infSeg + "+" + strings.Replace(modSeg, "M", "Es", 1)

			weakened = append(weakened, weaker)
		case mod%ModalEs == 0:
			weaker = infSeg + "+" + strings.Replace(modSeg, "Es", "En", 1)

			weakened = append(weakened, weaker)
		case mod%ModalEn == 0:
			weaker = infSeg + "+" + strings.Replace(modSeg, "En", "Ew", 1)

			weakened = append(weakened, weaker)
		case mod%ModalEw == 0:
			if weaker = infSeg + "+" + strings.Replace(modSeg, "Ew", "", 1); strings.HasSuffix(weaker, "+") {
				weakened = append(weakened, infSeg)
			} else {
				weakened = append(weakened, weaker)
			}
		}

		// Step down independent non-normal modal properties.
		if mod%ModalC == 0 {
			if weaker = infSeg + "+" + strings.Replace(modSeg, "C", "", 1); strings.HasSuffix(weaker, "+") {
				weakened = append(weakened, infSeg)
			} else {
				weakened = append(weakened, weaker)
			}
		}

		if mod%ModalN == 0 {
			if weaker = infSeg + "+" + strings.Replace(modSeg, "N", "", 1); strings.HasSuffix(weaker, "+") {
				weakened = append(weakened, infSeg)
			} else {
				weakened = append(weakened, weaker)
			}
		}

		// Step down modal extensions for normal and non-normal modal logics.
		if mod%ModalD == 0 {
			if weaker = infSeg + "+" + strings.Replace(modSeg, "D", "", 1); strings.HasSuffix(weaker, "+") {
				weakened = append(weakened, infSeg)
			} else {
				weakened = append(weakened, weaker)
			}
		}

		if mod%ModalT == 0 {
			if weaker = infSeg + "+" + strings.Replace(modSeg, "T", "", 1); strings.HasSuffix(weaker, "+") {
				weakened = append(weakened, infSeg)
			} else {
				weakened = append(weakened, weaker)
			}
		}

		if mod%Modal4 == 0 {
			if weaker = infSeg + "+" + strings.Replace(modSeg, "4", "", 1); strings.HasSuffix(weaker, "+") {
				weakened = append(weakened, infSeg)
			} else {
				weakened = append(weakened, weaker)
			}
		}

		if mod%ModalB == 0 {
			if weaker = infSeg + "+" + strings.Replace(modSeg, "B", "", 1); strings.HasSuffix(weaker, "+") {
				weakened = append(weakened, infSeg)
			} else {
				weakened = append(weakened, weaker)
			}
		}

		if mod%Modal5 == 0 {
			if weaker = infSeg + "+" + strings.Replace(modSeg, "5", "", 1); strings.HasSuffix(weaker, "+") {
				weakened = append(weakened, infSeg)
			} else {
				weakened = append(weakened, weaker)
			}
		}
	}

	weakened = gen.TupSet(weakened)

	return
}

type StrengthsTree struct {
	Inf      InfStrength
	Syn      SynBreadth
	Mod      ModStrength
	Name     string
	Branches []*StrengthsTree
}

func branchStrengthsTree(st *StrengthsTree) (nodes int) {
	var (
		name string
		inf  InfStrength
		mod  ModStrength
		stB  *StrengthsTree
	)

	for _, name = range WeakenLogic(st.Name) {
		inf, _, mod = ExtractLogic(name)

		stB = &StrengthsTree{
			Inf:      inf,
			Syn:      st.Syn,
			Mod:      mod,
			Name:     name,
			Branches: []*StrengthsTree{},
		}

		st.Branches = append(st.Branches, stB)

		nodes += 1 + branchStrengthsTree(stB)
	}

	return
}

func NewStrengthsTree(syn SynBreadth) (st *StrengthsTree, nodes int) {
	st = &StrengthsTree{
		Inf:      Classical,
		Syn:      syn,
		Mod:      ModalK * ModalD * ModalT * Modal4 * ModalB * Modal5,
		Name:     NameLogic(Classical, syn, ModalK*ModalD*ModalT*Modal4*ModalB*Modal5),
		Branches: []*StrengthsTree{},
	}

	nodes = 1 + branchStrengthsTree(st)

	return
}
