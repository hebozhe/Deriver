package fmla

import (
	"Deriver/gen"
	"slices"
	"strings"
	"unicode/utf8"
)

type Symbol rune
type Predicate rune
type Argument rune

const (
	NoSym Symbol = 0
	// Unary Connectives
	Neg Symbol = '¬'
	// Binary Connectives
	Wedge Symbol = '∧'
	Vee   Symbol = '∨'
	To    Symbol = '→'
	Iff   Symbol = '↔'
	// Quantifiers
	ForAll Symbol = '∀'
	Exists Symbol = '∃'
	// Modal Operators
	Box Symbol = '□'
	Dmd Symbol = '◇'
	// Parentheses
	LPar Symbol = '('
	RPar Symbol = ')'
	// Primitive Predicates
	NoPred Predicate = 0
	Equal  Predicate = '='
	Top    Predicate = '⊤'
	Bot    Predicate = '⊥'
	// Primtive Arguments
	NoArg Argument = 0
)

var Preds = []Predicate("ABCDEFGHIJKLMNOPQRSTUVWXYZ=⊤⊥")
var PredConsts = []Predicate("ABCDEFGHIJKLMNOPQRST=⊤⊥")
var SpecPredConsts = []Predicate("=⊤⊥")
var PredVars = []Predicate("UVWXYZ")

var Args = []Argument("abcdefghijklmnopqrstuvwxyz")
var ArgConsts = []Argument("abcdefghijklmnopqrst")
var ArgVars = []Argument("uvwxyz")

var UnaryOps = []Symbol{Neg, Box, Dmd}
var BinaryOps = []Symbol{Wedge, Vee, To, Iff}
var Quantifiers = []Symbol{Exists, ForAll}
var Ops = []Symbol{Neg, Box, Dmd, Wedge, Vee, To, Iff, Exists, ForAll}

type WffKind uint8

const (
	Atomic WffKind = iota + 1
	Unary
	Binary
	Quantified
)

type Wff struct {
	kind WffKind    // A kind of formula is Atomic, Unary, Binary, or Quantified.
	mop  Symbol     // If kind is Unary, Binary, or Quantified, this is the main operator.
	pv   Predicate  // If kind is Quantified, this is the predicate variable, if it exists.
	av   Argument   // If kind is Quantified, this is the argument variable, if it exists.
	pred Predicate  // If kind is Atomic, this is the predicate.
	args []Argument // If kind is Atomic, this is the tuple of arguments.

	subL *Wff // If kind is Unary, this is the sole operand; if Kind is Binary, this is the left operand.
	subR *Wff // If kind is Binary, this is the right operand.
	sup  *Wff // If this wff is a child, this is its parent.

	hash WffHash // The hash value of the WffTree.
}

func (wff *Wff) DeepCopy() (wffC *Wff) {
	if wff != nil {
		wffC = &Wff{
			kind: wff.kind,
			mop:  wff.mop,
			pv:   wff.pv,
			av:   wff.av,
			pred: wff.pred,
			args: wff.args,
			// subL: wff.subL, // The children are set below.
			// subR: wff.subR, // The children are set below.
			// sup:  nil, // The parent is set below.
			hash: wff.hash,
		}

		if wff.subL != nil {
			wffC.subL = wff.subL.DeepCopy()

			wffC.subL.sup = wffC
		}

		if wff.subR != nil {
			wffC.subR = wff.subR.DeepCopy()

			wffC.subR.sup = wffC
		}
	}

	return
}

func (wff *Wff) Kind() (kind WffKind) {
	if wff == nil {
		panic("Missing formula.")
	}

	kind = wff.kind

	return
}

func (wff *Wff) Mop() (mop Symbol) {
	if wff == nil {
		panic("Missing formula.")
	}

	mop = wff.mop

	return
}

func (wff *Wff) Var() (pv Predicate, av Argument, ok bool) {
	if wff == nil {
		panic("Missing formula.")
	}

	if wff.kind == Quantified {
		if ok = wff.pv != NoPred; ok {
			pv = wff.pv
		} else if ok = wff.av != NoArg; ok {
			av = wff.av
		}
	}

	return
}

func (wff *Wff) SubL() (subL *Wff) {
	if wff == nil {
		panic("Missing formula.")
	}

	if wff.subL != nil {
		subL = wff.subL.DeepCopy()
	}

	return
}

func (wff *Wff) SubR() (subR *Wff) {
	if wff == nil {
		panic("Missing formula.")
	}

	if wff.subR != nil {
		subR = wff.subR.DeepCopy()
	}

	return
}

func (wff *Wff) Subs() (subL, subR *Wff, arity int) {
	if wff == nil {
		panic("Missing formula.")
	}

	if subL, subR = wff.SubL(), wff.SubR(); subR != nil {
		arity = 2
	} else if subL != nil {
		arity = 1
	}

	return
}

func (wff *Wff) Locate(loc string) (sub *Wff) {
	var (
		r rune
	)

	sub = wff

	for _, r = range loc {
		switch r {
		case 'L':
			sub = sub.subL
		case 'R':
			sub = sub.subR
		default:
			panic("Only 'L' (left) and 'R' (right) may locate subs.")
		}

		if sub == nil {
			break
		}
	}

	sub = sub.DeepCopy()

	return
}

func allSubs(wff *Wff, unique bool, setU map[WffHash]bool) (subs []*Wff) {
	var (
		subL, subR   *Wff
		subsL, subsR []*Wff
		arity        int
	)

	if setU == nil {
		setU = map[WffHash]bool{}
	}

	if !unique || !setU[wff.hash] {
		subs = append(subs, wff.DeepCopy())

		if unique {
			setU[wff.hash] = true
		}

		subL, subR, arity = wff.Subs()

		switch arity {
		case 1:
			subsL = allSubs(subL, false, setU)

			subs = append(subs, subsL...)
		case 2:
			subsL, subsR = allSubs(subL, unique, setU), allSubs(subR, false, setU)

			subs = append(subs, subsL...)
			subs = append(subs, subsR...)
		}
	}

	return
}

func (wff *Wff) AllSubs(unique, closed bool) (subs []*Wff) {
	if wff == nil {
		panic("Missing formula.")
	}

	subs = allSubs(wff, unique, nil)

	if closed {
		subs = slices.DeleteFunc(subs, func(sub *Wff) (nix bool) {
			nix = !sub.IsClosed()

			return
		})
	}

	return
}

func (wff *Wff) Hash() (h WffHash) {
	if wff == nil {
		panic("Missing formula.")
	}

	h = wff.hash

	return
}

func (wff *Wff) Pred() (pred Predicate) {
	if wff == nil {
		panic("Missing formula.")
	}

	if wff.kind == Atomic {
		pred = wff.pred
	}

	return
}

func (wff *Wff) Args() (args []Argument) {
	if wff == nil {
		panic("Missing formula.")
	}

	if wff.kind == Atomic {
		args = append(args, wff.args...)
	}

	return
}

func (wff *Wff) Valency() (valency int) {
	if wff == nil {
		panic("Missing formula.")
	}

	if wff.kind == Atomic {
		valency = len(wff.args)
	}

	return
}

func (wff *Wff) AllPreds(unique bool) (pcs, pvs []Predicate) {
	var (
		pcsL, pcsR, pvsL, pvsR []Predicate
	)

	if wff == nil {
		panic("Missing formula.")
	}

	switch wff.kind {
	case Atomic:
		if slices.Contains(PredConsts, wff.pred) {
			pcs = []Predicate{wff.pred}
		} else if slices.Contains(PredVars, wff.pred) {
			pvs = []Predicate{wff.pred}
		}
	default:
		if wff.subL != nil {
			pcsL, pvsL = wff.subL.AllPreds(false)
		}

		if wff.subR != nil {
			pcsR, pvsR = wff.subR.AllPreds(false)
		}

		pcs = append(pcs, pcsL...)
		pcs = append(pcs, pcsR...)

		pvs = append(pvs, pvsL...)
		pvs = append(pvs, pvsR...)
	}

	if unique {
		pcs, pvs = gen.TupSet(pcs), gen.TupSet(pvs)
	}

	return
}

func (wff *Wff) AllArgs(unique bool) (acs, avs []Argument) {
	var (
		acsL, acsR, avsL, avsR []Argument
		arg                    Argument
	)

	if wff == nil {
		panic("Missing formula.")
	}

	switch wff.kind {
	case Atomic:
		for _, arg = range wff.args {
			if slices.Contains(ArgConsts, arg) {
				acs = append(acs, arg)
			} else if slices.Contains(ArgVars, arg) {
				avs = append(avs, arg)
			}
		}
	default:
		if wff.subL != nil {
			acsL, avsL = wff.subL.AllArgs(false)
		}

		if wff.subR != nil {
			acsR, avsR = wff.subR.AllArgs(false)
		}

		acs = append(acs, acsL...)
		acs = append(acs, acsR...)

		avs = append(avs, avsL...)
		avs = append(avs, avsR...)
	}

	if unique {
		acs, avs = gen.TupSet(acs), gen.TupSet(avs)
	}

	return
}

func (wff *Wff) AllVars(unique bool) (pvs []Predicate, avs []Argument) {
	var (
		pvsL, pvsR []Predicate
		avsL, avsR []Argument
		arg        Argument
	)

	if wff == nil {
		panic("Missing formula.")
	}

	switch wff.kind {
	case Atomic:
		if slices.Contains(PredVars, wff.pred) {
			pvs = []Predicate{wff.pred}
		}

		for _, arg = range wff.args {
			if slices.Contains(ArgVars, arg) {
				avs = append(avs, arg)
			}
		}
	default:
		if wff.subL != nil {
			pvsL, avsL = wff.subL.AllVars(false)
		}

		if wff.subR != nil {
			pvsR, avsR = wff.subR.AllVars(false)
		}

		pvs = append(pvs, pvsL...)
		pvs = append(pvs, pvsR...)

		avs = append(avs, avsL...)
		avs = append(avs, avsR...)
	}

	if unique {
		pvs, avs = gen.TupSet(pvs), gen.TupSet(avs)
	}

	return
}

func (wff *Wff) AllConsts(unique bool) (pcs []Predicate, acs []Argument) {
	var (
		arg        Argument
		pcsL, pcsR []Predicate
		acsL, acsR []Argument
	)

	if wff == nil {
		panic("Missing formula.")
	}

	switch wff.kind {
	case Atomic:
		if slices.Contains(PredConsts, wff.pred) {
			pcs = []Predicate{wff.pred}
		}

		for _, arg = range wff.args {
			if slices.Contains(ArgConsts, arg) {
				acs = append(acs, arg)
			}
		}
	default:
		if wff.subL != nil {
			pcsL, acsL = wff.subL.AllConsts(false)
		}

		if wff.subR != nil {
			pcsR, acsR = wff.subR.AllConsts(false)
		}

		pcs = append(pcs, pcsL...)
		pcs = append(pcs, pcsR...)

		acs = append(acs, acsL...)
		acs = append(acs, acsR...)
	}

	if unique {
		pcs, acs = gen.TupSet(pcs), gen.TupSet(acs)
	}

	return
}

func (wff *Wff) String() (s string) {
	var (
		sL, sR string
	)

	if wff == nil {
		panic("Missing formula.")
	}

	switch wff.kind {
	case Atomic:
		switch wff.pred {
		case Top, Bot:
			s = string(wff.pred)
		case Equal:
			s = string(wff.args[0]) + string(wff.pred) + string(wff.args[1])
		default:
			s = string(wff.pred) + string(wff.args)
		}
	case Unary:
		if wff.subL.kind == Binary {
			s = string(wff.mop) + "(" + wff.subL.String() + ")"
		} else {
			s = string(wff.mop) + wff.subL.String()
		}
	case Binary:
		if wff.subL.kind == Binary {
			sL = "(" + wff.subL.String() + ")"
		} else {
			sL = wff.subL.String()
		}

		if wff.subR.kind == Binary {
			sR = "(" + wff.subR.String() + ")"
		} else {
			sR = wff.subR.String()
		}

		s = sL + string(wff.mop) + sR
	case Quantified:
		if wff.subL.kind == Binary {
			sL = "(" + wff.subL.String() + ")"
		} else {
			sL = wff.subL.String()
		}

		if wff.pv != NoPred {
			s = string(wff.mop) + string(wff.pv) + sL
		} else if wff.av != NoArg {
			s = string(wff.mop) + string(wff.av) + sL
		}
	default:
		panic("Unsupported formula kind.")
	}

	return
}

func (wff *Wff) Len() (lenW uint) {
	var s string

	if wff == nil {
		panic("Missing formula.")
	}

	s = wff.String()

	lenW = uint(utf8.RuneCountInString(s))

	return
}

func (wff *Wff) Depth() (depW uint) {
	var (
		depL, depR uint
	)

	if wff == nil {
		panic("Missing formula.")
	}

	switch wff.kind {
	case Atomic:
		depW = 1
	default:
		if wff.subL != nil {
			depL = wff.subL.Depth()
		}

		if wff.subR != nil {
			depR = wff.subR.Depth()
		}

		depW = 1 + max(depL, depR)
	}

	return
}

func (wffA *Wff) Is(wffB *Wff) (is bool) {
	if wffA == nil || wffB == nil {
		panic("Missing formula.")
	}

	is = wffA.hash == wffB.hash

	return
}

type WffPart interface {
	*Wff | Symbol | Predicate | Argument | string | rune
}

func hasSub(wff, sub *Wff) (has bool) {
	if has = wff.Is(sub); !has {
		has = (wff.subL != nil && hasSub(wff.subL, sub)) || (wff.subR != nil && hasSub(wff.subR, sub))
	}

	return
}

func hasOp(wff *Wff, op Symbol) (has bool) {
	if has = wff.mop == op; !has {
		has = (wff.subL != nil && hasOp(wff.subL, op)) || (wff.subR != nil && hasOp(wff.subR, op))
	}

	return
}

func hasPred(wff *Wff, pred Predicate) (has bool) {
	switch wff.kind {
	case Atomic:
		has = wff.pred == pred
	default:
		has = (wff.subL != nil && hasPred(wff.subL, pred)) || (wff.subR != nil && hasPred(wff.subR, pred))
	}

	return
}

func hasArg(wff *Wff, arg Argument) (has bool) {
	switch wff.kind {
	case Atomic:
		has = slices.Contains(wff.args, arg)
	default:
		has = (wff.subL != nil && hasArg(wff.subL, arg)) || (wff.subR != nil && hasArg(wff.subR, arg))
	}

	return
}

func (wff *Wff) Has[P WffPart](this P) (has bool) {
	if wff == nil {
		panic("Missing formula.")
	}

	switch val := any(this).(type) {
	case *Wff:
		has = hasSub(wff, val)
	case Symbol:
		has = hasOp(wff, val)
	case Predicate:
		has = hasPred(wff, val)
	case Argument:
		has = hasArg(wff, val)
	case string:
		has = strings.Contains(wff.String(), val)
	case rune:
		has = strings.ContainsRune(wff.String(), val)
	}

	return
}

func isClosed(wff *Wff, pvs []Predicate, avs []Argument) (is bool) {
	var (
		arg Argument
	)

	switch wff.kind {
	case Atomic:
		if is = slices.Contains(PredConsts, wff.pred) || slices.Contains(pvs, wff.pred); is {
			for _, arg = range wff.args {
				if is = slices.Contains(ArgConsts, arg) || slices.Contains(avs, arg); !is {
					break
				}
			}
		}
	default:
		if wff.pv != NoPred {
			pvs = append(pvs, wff.pv)
		} else if wff.av != NoArg {
			avs = append(avs, wff.av)
		}

		is = (wff.subL == nil || isClosed(wff.subL, pvs, avs)) && (wff.subR == nil || isClosed(wff.subR, pvs, avs))
	}

	return
}

func (wff *Wff) IsClosed() (is bool) {
	if wff == nil {
		panic("Missing formula.")
	}

	is = isClosed(wff, nil, nil)

	return
}

func (wff *Wff) IsVacuous() (is bool) {
	if wff == nil {
		panic("Missing formula.")
	}

	if wff.kind == Quantified {
		switch {
		case wff.pv != NoPred:
			is = wff.Instantiate(PredConsts[0]).Is(wff.subL)
		case wff.av != NoArg:
			is = wff.Instantiate(ArgConsts[0]).Is(wff.subL)
		default:
			panic("Missing quantified variable.")
		}
	} else {
		panic("The formula is not quantified.")
	}

	return
}
