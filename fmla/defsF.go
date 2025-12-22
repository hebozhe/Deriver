package fmla

import (
	"slices"
	"unicode/utf8"
)

type Symbol rune
type Connective Symbol
type Quantifier Symbol
type Predicate Symbol
type Argument Symbol

const (
	// Unary Connectives
	Neg Connective = '¬'
	// Binary Connectives
	Wedge Connective = '∧'
	Vee   Connective = '∨'
	To    Connective = '→'
	Iff   Connective = '↔'
	// Quantifiers
	Exists Quantifier = '∃'
	ForAll Quantifier = '∀'
	// Modal Operators
	Box     Connective = '□'
	Diamond Connective = '◇'
	// Parentheses
	LPar Symbol = '('
	RPar Symbol = ')'
	// Primitive Operands
	Equals Predicate = '='
	Top    Predicate = '⊤'
	Bot    Predicate = '⊥'
)

var PredConsts = []Predicate("ABCDEFGHIJKLMNOPQRST")
var PredVars = []Predicate("UVWXYZ")

var ArgConsts = []Argument("abcdefghijklmnopqrst")
var ArgVars = []Argument("uvwxyz")

var UnaryOps = []Connective{Neg, Box, Diamond}
var BinaryOps = []Connective{Wedge, Vee, To, Iff}
var Quantifiers = []Quantifier{Exists, ForAll}

type WffKind int

const (
	Atomic WffKind = iota + 1
	Unary
	Binary
	Quantified
)

type WffTree struct {
	kind WffKind    // A kind of formula is Atomic, Unary, Binary, or Quantified.
	mop  Symbol     // If Kind is Unary, Binary, or Quantified, this is the main operator.
	pVar Predicate  // If Kind is Quantified, this is the predicate variable, if it exists.
	aVar Argument   // If Kind is Quantified, this is the argument variable, if it exists.
	pred Predicate  // If Kind is Atomic, this is the predicate.
	args []Argument // If Kind is Atomic, this is the tuple of arguments.
	subL *WffTree   // If Kind is Unary, this is the sole operand; if Kind is Binary, this is the left operand.
	subR *WffTree   // If Kind is Binary, this is the right operand.
	sup  *WffTree   // If SubL is non-nil, this is the super-formula.
}

func GetWffKind(wff *WffTree) (kind WffKind) {
	kind = wff.kind

	return
}

func GetWffMainOperator(wff *WffTree) (con Connective, qua Quantifier, ok bool) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	if ok = wff.kind != Atomic; ok {
		switch {
		case slices.Contains(UnaryOps, Connective(wff.mop)):
			con = Connective(wff.mop)
		case slices.Contains(BinaryOps, Connective(wff.mop)):
			con = Connective(wff.mop)
		case slices.Contains(Quantifiers, Quantifier(wff.mop)):
			qua = Quantifier(wff.mop)
		}
	}

	return
}

func GetWffQuaAndVars(wff *WffTree) (qua Quantifier, pVar Predicate, aVar Argument, ok bool) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	if ok = wff.kind == Quantified; ok {
		qua = Quantifier(wff.mop)
		pVar = wff.pVar
		aVar = wff.aVar
	}

	return
}

func GetWffSubformulae(wff *WffTree) (subL, subR *WffTree, ok bool) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	if ok = wff.kind != Atomic; ok {
		subL = DeepCopy(wff.subL)
		subR = DeepCopy(wff.subR)
	}

	return
}

func GetWffSuperFormula(wff *WffTree) (sup *WffTree) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	sup = DeepCopy(wff.sup)

	return
}

func GetWffPredAndArgs(wff *WffTree) (pred Predicate, args []Argument, ok bool) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	if ok = wff.kind == Atomic; ok {
		pred = wff.pred
		args = append(args, wff.args...)
	}

	return
}

func GetConstants(wff *WffTree) (pcs []Predicate, acs []Argument) {
	var (
		pcsL, pcsR []Predicate
		acsL, acsR []Argument
		ac         Argument
	)

	switch wff.kind {
	case Atomic:
		if 'A'-1 < wff.pred && wff.pred < 'T'+1 {
			pcs = append(pcs, wff.pred)
		}

		for _, ac = range wff.args {
			if 'a'-1 < ac && ac < 't'+1 {
				acs = append(acs, ac)
			}
		}
	case Unary:
		pcsL, acsL = GetConstants(wff.subL)

		pcs = append(pcs, pcsL...)

		acs = append(acs, acsL...)
	case Binary:
		pcsL, acsL = GetConstants(wff.subL)

		pcsR, acsR = GetConstants(wff.subR)

		pcs = append(pcs, pcsL...)
		pcs = append(pcs, pcsR...)

		acs = append(acs, acsL...)
		acs = append(acs, acsR...)
	case Quantified:
		pcsL, acsL = GetConstants(wff.subL)

		pcs = append(pcs, pcsL...)

		acs = append(acs, acsL...)
	default:
		panic("Invalid WffTree")
	}

	pcs = slices.DeleteFunc(pcs, func(pc Predicate) (nix bool) {
		var dex int = slices.Index(pcs, pc)

		nix = -1 < dex && slices.Contains(pcs[dex+1:], pc)

		return
	})

	acs = slices.DeleteFunc(acs, func(ac Argument) (nix bool) {
		var dex int = slices.Index(acs, ac)

		nix = -1 < dex && slices.Contains(acs[dex+1:], ac)

		return
	})

	return
}

func GetVariables(wff *WffTree) (pvs []Predicate, avs []Argument) {
	var (
		pvsL, pvsR []Predicate
		avsL, avsR []Argument
		av         Argument
	)

	switch wff.kind {
	case Atomic:
		if 'U'-1 < wff.pred && wff.pred < 'Z'+1 {
			pvs = append(pvs, wff.pred)
		}

		for _, av = range wff.args {
			if 'u'-1 < av && av < 'z'+1 {
				avs = append(avs, av)
			}
		}
	case Unary:
		pvsL, avsL = GetVariables(wff.subL)

		pvs = append(pvs, pvsL...)

		avs = append(avs, avsL...)
	case Binary:
		pvsL, avsL = GetVariables(wff.subL)

		pvsR, avsR = GetVariables(wff.subR)

		pvs = append(pvs, pvsL...)
		pvs = append(pvs, pvsR...)

		avs = append(avs, avsL...)
		avs = append(avs, avsR...)
	case Quantified:
		if wff.pVar != 0 {
			pvs = append(pvs, wff.pVar)
		}

		if wff.aVar != 0 {
			avs = append(avs, wff.aVar)
		}
	default:
		panic("Invalid WffTree")
	}

	pvs = slices.DeleteFunc(pvs, func(pv Predicate) (nix bool) {
		var dex int = slices.Index(pvs, pv)

		nix = -1 < dex && slices.Contains(pvs[dex+1:], pv)

		return
	})

	avs = slices.DeleteFunc(avs, func(av Argument) (nix bool) {
		var dex int = slices.Index(avs, av)

		nix = -1 < dex && slices.Contains(avs[dex+1:], av)

		return
	})

	return
}

func GetWffString(wff *WffTree) (s string) {
	var (
		wffL, wffR string
		lenA       int
	)

	switch wff.kind {
	case Atomic:
		switch wff.pred {
		case Top, Bot:
			s = string(wff.pred)
		case Equals:
			if lenA = len(wff.args); lenA != 2 {
				panic("Equals predicate requires exactly two arguments")
			}

			s = string(wff.args[0]) + string(wff.pred) + string(wff.args[1])
		default:
			s = string(wff.pred) + string(wff.args)
		}
	case Unary:
		if wff.subL.kind == Binary {
			s = string(wff.mop) + "(" + GetWffString(wff.subL) + ")"
		} else {
			s = string(wff.mop) + GetWffString(wff.subL)
		}

	case Binary:
		if wff.subL.kind == Binary {
			wffL = "(" + GetWffString(wff.subL) + ")"
		} else {
			wffL = GetWffString(wff.subL)
		}

		if wff.subR.kind == Binary {
			wffR = "(" + GetWffString(wff.subR) + ")"
		} else {
			wffR = GetWffString(wff.subR)
		}

		s = wffL + string(wff.mop) + wffR
	case Quantified:
		if wff.subL.kind == Binary {
			wffL = "(" + GetWffString(wff.subL) + ")"
		} else {
			wffL = GetWffString(wff.subL)
		}

		if wff.pVar != 0 {
			s = string(wff.mop) + string(wff.pVar) + wffL
		} else if wff.aVar != 0 {
			s = string(wff.mop) + string(wff.aVar) + wffL
		}
	default:
		panic("Invalid WffTree")
	}

	return
}

func GetWffLength(wff *WffTree) (lenW uint) {
	var s string = GetWffString(wff)

	lenW = uint(utf8.RuneCountInString(s))

	return
}

func GetWffDepth(wff *WffTree) (depW uint) {
	switch wff.kind {
	case Atomic:
		depW = 1
	case Unary:
		depW = GetWffDepth(wff.subL) + 1
	case Binary:
		depW = max(GetWffDepth(wff.subL), GetWffDepth(wff.subR)) + 1
	case Quantified:
		depW = GetWffDepth(wff.subL) + 1
	default:
		panic("Invalid WffTree")
	}

	return
}
