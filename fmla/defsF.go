package fmla

import (
	"slices"
	"strings"
	"unicode/utf8"
)

type Symbol rune
type Predicate rune
type Argument rune

type ArgString string

const (
	NoSymbol Symbol = 0
	// Unary Connectives
	Neg Symbol = '¬'
	// Binary Connectives
	Wedge Symbol = '∧'
	Vee   Symbol = '∨'
	To    Symbol = '→'
	Iff   Symbol = '↔'
	// Quantifiers
	Exists Symbol = '∃'
	ForAll Symbol = '∀'
	// Modal Operators
	Box     Symbol = '□'
	Diamond Symbol = '◇'
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

var UnaryOps = []Symbol{Neg, Box, Diamond}
var BinaryOps = []Symbol{Wedge, Vee, To, Iff}
var Quantifiers = []Symbol{Exists, ForAll}

type WffKind int

const (
	Atomic WffKind = iota + 1
	Unary
	Binary
	Quantified
)

type WffTree struct {
	kind WffKind   // A kind of formula is Atomic, Unary, Binary, or Quantified.
	mop  Symbol    // If Kind is Unary, Binary, or Quantified, this is the main operator.
	pv   Predicate // If Kind is Quantified, this is the predicate variable, if it exists.
	av   Argument  // If Kind is Quantified, this is the argument variable, if it exists.
	pred Predicate // If Kind is Atomic, this is the predicate.
	args ArgString // If Kind is Atomic, this is the tuple of arguments.
	subL *WffTree  // If Kind is Unary, this is the sole operand; if Kind is Binary, this is the left operand.
	subR *WffTree  // If Kind is Binary, this is the right operand.
	sup  *WffTree  // If SubL is non-nil, this is the super-formula.

	h WffHash // The hash value of the WffTree.
}

func argStringToArgs(s ArgString) (args []Argument) {
	var (
		r rune
	)

	for _, r = range s {
		args = append(args, Argument(r))
	}

	return
}

func argsToArgString(args ...Argument) (s ArgString) {
	var (
		a Argument
	)

	for _, a = range args {
		s += ArgString(a)
	}

	return
}

func GetWffKind(wff *WffTree) (kind WffKind) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	kind = wff.kind

	return
}

func GetWffMop(wff *WffTree) (sym Symbol) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	sym = wff.mop

	return
}

func GetWffOps(wff *WffTree) (ops []Symbol) {
	var (
		opsL, opsR []Symbol
	)

	if wff == nil {
		panic("Invalid WffTree")
	}

	ops = append(ops, wff.mop)

	switch wff.kind {
	case Atomic:
		ops = append(ops, NoSymbol)
	case Unary:
		opsL = GetWffOps(wff.subL)

		ops = append(ops, opsL...)
	case Binary:
		opsL, opsR = GetWffOps(wff.subL), GetWffOps(wff.subR)

		ops = append(ops, opsL...)
		ops = append(ops, opsR...)
	case Quantified:
		opsL = GetWffOps(wff.subL)

		ops = append(ops, opsL...)
	default:
		panic("Invalid WffTree")
	}

	return
}

func GetWffVars(wff *WffTree) (pv Predicate, av Argument) {
	if wff == nil || wff.kind != Quantified {
		panic("Invalid WffTree")
	}

	if wff.pv == 0 && wff.av == 0 {
		panic("No predicate or argument variable.")
	}

	if wff.pv != 0 && wff.av != 0 {
		panic("Both predicate and argument variables exist.")
	}

	pv, av = wff.pv, wff.av

	return
}

func GetWffSubformulae(wff *WffTree) (subL, subR *WffTree) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	subL, subR = DeepCopy(wff.subL), DeepCopy(wff.subR)

	return
}

func GetWffSuperformula(wff *WffTree) (sup *WffTree) {
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
		args = argStringToArgs(wff.args)
	}

	return
}

func RemoveRedundantEntries(preds []Predicate, args []Argument) (predsU []Predicate, argsU []Argument) {
	var (
		predsMap map[Predicate]bool
		argsMap  map[Argument]bool
		pred     Predicate
		arg      Argument
	)

	predsMap, argsMap = map[Predicate]bool{}, map[Argument]bool{}

	for _, pred = range preds {
		if !predsMap[pred] {
			predsU = append(predsU, pred)

			predsMap[pred] = true
		}
	}

	for _, arg = range args {
		if !argsMap[arg] {
			argsU = append(argsU, arg)

			argsMap[arg] = true
		}
	}

	return
}

func GetConstants(wff *WffTree) (pcs []Predicate, acs []Argument) {
	var (
		pcsL, pcsR []Predicate
		acsL, acsR []Argument
		arg        Argument
	)

	switch wff.kind {
	case Atomic:
		if 'A'-1 < wff.pred && wff.pred < 'T'+1 {
			pcs = append(pcs, wff.pred)
		}

		for _, arg = range argStringToArgs(wff.args) {
			if 'a'-1 < arg && arg < 't'+1 {
				acs = append(acs, arg)
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

	if wff.sup == nil {
		pcs, acs = RemoveRedundantEntries(pcs, acs)
	}

	return
}

func GetVariables(wff *WffTree) (pvs []Predicate, avs []Argument) {
	var (
		pvsL, pvsR []Predicate
		avsL, avsR []Argument
		arg        Argument
	)

	switch wff.kind {
	case Atomic:
		if 'U'-1 < wff.pred && wff.pred < 'Z'+1 {
			pvs = append(pvs, wff.pred)
		}

		for _, arg = range argStringToArgs(wff.args) {
			if 'u'-1 < arg && arg < 'z'+1 {
				avs = append(avs, arg)
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
		if wff.pv != 0 {
			pvs = append(pvs, wff.pv)
		}

		if wff.av != 0 {
			avs = append(avs, wff.av)
		}

		pvsL, avsL = GetVariables(wff.subL)

		pvs = append(pvs, pvsL...)

		avs = append(avs, avsL...)
	default:
		panic("Invalid WffTree")
	}

	if wff.sup == nil {
		pvs, avs = RemoveRedundantEntries(pvs, avs)
	}

	return
}

func GetFreeVariables(wff *WffTree) (pvs []Predicate, avs []Argument) {
	var (
		pvsL, pvsR []Predicate
		avsL, avsR []Argument
		arg        Argument
	)

	switch wff.kind {
	case Atomic:
		if 'U'-1 < wff.pred && wff.pred < 'Z'+1 {
			pvs = append(pvs, wff.pred)
		}

		for _, arg = range argStringToArgs(wff.args) {
			if 'u'-1 < arg && arg < 'z'+1 {
				avs = append(avs, arg)
			}
		}
	case Unary:
		pvsL, avsL = GetFreeVariables(wff.subL)

		pvs = append(pvs, pvsL...)

		avs = append(avs, avsL...)
	case Binary:
		pvsL, avsL = GetFreeVariables(wff.subL)

		pvsR, avsR = GetFreeVariables(wff.subR)

		pvs = append(pvs, pvsL...)
		pvs = append(pvs, pvsR...)

		avs = append(avs, avsL...)
		avs = append(avs, avsR...)
	case Quantified:
		// Collect the variables from the subformula.
		pvsL, avsL = GetFreeVariables(wff.subL)

		pvs = append(pvs, pvsL...)

		avs = append(avs, avsL...)

		// Remove the bound variable from the variables.
		if wff.pv != 0 {
			pvs = slices.DeleteFunc(pvs, func(pv Predicate) (nix bool) {
				nix = pv == wff.pv

				return
			})
		}

		if wff.av != 0 {
			avs = slices.DeleteFunc(avs, func(av Argument) (nix bool) {
				nix = av == wff.av

				return
			})
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

	if wff == nil {
		panic("Invalid WffTree")
	}

	switch wff.kind {
	case Atomic:
		switch wff.pred {
		case Top, Bot:
			s = string(wff.pred)
		case Equals:
			if lenA = len(argStringToArgs(wff.args)); lenA != 2 {
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

		if wff.pv != 0 {
			s = string(wff.mop) + string(wff.pv) + wffL
		} else if wff.av != 0 {
			s = string(wff.mop) + string(wff.av) + wffL
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
	var (
		depL, depR uint
	)

	switch wff.kind {
	case Atomic:
		depW = 1
	case Unary, Quantified:
		depW = GetWffDepth(wff.subL) + 1
	case Binary:
		depL, depR = GetWffDepth(wff.subL), GetWffDepth(wff.subR)

		depW = max(depL, depR) + 1
	default:
		panic("Invalid WffTree")
	}

	return
}

func HasPred(wff *WffTree, pred Predicate) (has bool) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	switch wff.kind {
	case Atomic:
		has = wff.pred == pred
	case Unary:
		has = HasPred(wff.subL, pred)
	case Binary:
		has = HasPred(wff.subL, pred) || HasPred(wff.subR, pred)
	case Quantified:
		has = HasPred(wff.subL, pred)
	default:
		panic("Invalid WffTree")
	}

	return
}

func HasArg(wff *WffTree, arg Argument) (has bool) {
	var args []Argument

	if wff == nil {
		panic("Invalid WffTree")
	}

	switch wff.kind {
	case Atomic:
		args = argStringToArgs(wff.args)

		has = slices.Contains(args, arg)
	case Unary:
		has = HasArg(wff.subL, arg)
	case Binary:
		has = HasArg(wff.subL, arg) || HasArg(wff.subR, arg)
	case Quantified:
		has = HasArg(wff.subL, arg)
	default:
		panic("Invalid WffTree")
	}

	return
}

func HasOp(wff *WffTree, op Symbol) (has bool) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	switch wff.kind {
	case Atomic:
		has = wff.mop == op // Trivially true with NoSymbol.
	case Unary:
		has = wff.mop == op || HasOp(wff.subL, op)
	case Binary:
		has = wff.mop == op || HasOp(wff.subL, op) || HasOp(wff.subR, op)
	case Quantified:
		has = wff.mop == op || HasOp(wff.subL, op)
	default:
		panic("Invalid WffTree")
	}

	return
}

func CountOps(wff *WffTree, op Symbol) (count uint) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	if wff.mop == op {
		count = 1
	}

	switch wff.kind {
	case Atomic:
		// Trivially true with NoSymbol.
	case Unary:
		count += CountOps(wff.subL, op)
	case Binary:
		count += CountOps(wff.subL, op) + CountOps(wff.subR, op)
	case Quantified:
		count += CountOps(wff.subL, op)
	default:
		panic("Invalid WffTree")
	}

	return
}

func HasFreeVars(wff *WffTree) (has bool) {
	var (
		pvs        []Predicate
		avs        []Argument
		lenP, lenA int
	)

	if wff == nil {
		panic("Invalid WffTree")
	}

	pvs, avs = GetFreeVariables(wff)

	if lenP, lenA = len(pvs), len(avs); 0 < lenP+lenA {
		has = true
	}

	return
}

func FindSubformula(wff *WffTree, sub *WffTree) (s string) {
	var (
		sL, sR string
	)

	if wff == nil {
		panic("Invalid WffTree")
	}

	if IsIdentical(wff, sub) {
		s = "!"
	} else {
		switch wff.kind {
		case Atomic:
			// Do nothing. There was no match.
		case Unary:
			sL = FindSubformula(wff.subL, sub)

			if strings.HasSuffix(sL, "!") {
				s = "L" + sL
			}
		case Binary:
			sL, sR = FindSubformula(wff.subL, sub), FindSubformula(wff.subR, sub)

			if strings.HasSuffix(sL, "!") {
				sL = "L" + sL
			} else if strings.HasSuffix(sR, "!") {
				sR = "R" + sR
			}

			switch {
			case sL != "" && sR != "":
				if len(sR) < len(sL) {
					s = sR
				} else {
					s = sL
				}
			case sL != "":
				s = sL
			case sR != "":
				s = sR
			}
		case Quantified:
			sL = FindSubformula(wff.subL, sub)

			if strings.HasSuffix(sL, "!") {
				s = "L" + sL
			}
		default:
			panic("Invalid WffTree")
		}
	}

	return
}

func RetrieveSubformula(wff *WffTree, s string) (sub *WffTree) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	switch {
	case strings.HasPrefix(s, "L"):
		switch wff.kind {
		case Unary, Binary, Quantified:
			sub = RetrieveSubformula(wff.subL, s[1:])
		}
	case strings.HasPrefix(s, "R"):
		switch wff.kind {
		case Binary:
			sub = RetrieveSubformula(wff.subR, s[1:])
		}
	case strings.HasPrefix(s, "!"):
		sub = DeepCopy(wff)
	default:
		panic("Invalid retrieval string.")
	}

	return
}
