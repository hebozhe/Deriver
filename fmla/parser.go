package fmla

import (
	"regexp"
	"slices"
	"strings"
)

type convStruct struct {
	from string
	sym  Symbol
	pred Predicate
}

type parser struct {
	s    string
	syms []Symbol
	deps []int
	wffs []*WffTree
}

var (
	rexWS   = regexp.MustCompile(`\s`)
	rexBase = regexp.MustCompile(`^[A-Z][a-z]*$`)
	rexTorF = regexp.MustCompile(`^(⊤|⊥)$`)
	rexIden = regexp.MustCompile(`^[a-z]=[a-z]$`)
)

func convertNotation(sA string) (sB string, ok bool) {
	var (
		convs []convStruct
		conv  convStruct
		rB    rune
		chrs  string
	)

	sB = rexWS.ReplaceAllString(sA, "")

	convs = []convStruct{
		// Three-character transformations:
		{from: "<->", sym: Iff},
		// Two-character transformations:
		{from: "->", sym: To},
		{from: "\\/", sym: Vee},
		{from: "/\\", sym: Wedge},
		{from: "[]", sym: Box},
		{from: "<>", sym: Diamond},
		// One-character transformations:
		{from: "~", sym: Neg},
		{from: "$", sym: Exists},
		{from: "@", sym: ForAll},
		{from: "^", pred: Top},
		{from: "#", pred: Bot},
		{from: "{", sym: LPar},
		{from: "}", sym: RPar},
		{from: "[", sym: LPar},
		{from: "]", sym: RPar},
	}

	for _, conv = range convs {
		if conv.sym != 0 {
			sB = strings.ReplaceAll(sB, conv.from, string(conv.sym))
		}

		if conv.pred != 0 {
			sB = strings.ReplaceAll(sB, conv.from, string(conv.pred))
		}
	}

	chrs = string(PredConsts) + string(PredVars) +
		string(ArgConsts) + string(ArgVars) +
		string(UnaryOps) + string(BinaryOps) + string(Quantifiers) +
		string(LPar) + string(RPar) +
		string(Top) + string(Bot) + string(Equals)

	ok = true

	for _, rB = range sB {
		if ok = strings.ContainsRune(chrs, rB); !ok {
			break
		}
	}

	return
}

func newParser(s string) (prs *parser, ok bool) {
	var (
		sym         Symbol
		depth, lenS int
	)

	prs = &parser{
		s:    s,
		syms: []Symbol(s),
		deps: []int{},
		wffs: []*WffTree{},
	}

	for _, sym = range prs.syms {
		switch sym {
		case LPar:
			depth += 1
		case RPar:
			depth -= 1
		}

		prs.deps = append(prs.deps, depth)
	}

	lenS = len(prs.syms)

	ok = 0 < lenS &&
		!slices.Contains(prs.deps, -1) &&
		prs.deps[lenS-1] == 0

	if ok &&
		prs.syms[0] == LPar &&
		!slices.Contains(prs.deps[1:lenS-1], 0) &&
		prs.syms[lenS-1] == RPar {
		s = string(prs.syms[1 : lenS-1])

		prs, ok = newParser(s)
	}

	return
}

func findMainOperator(prs *parser) (mop Symbol, dexM int, ok bool) {
	var (
		dexesB           []int
		sym, unop, binop Symbol
		dexS, lenS, lenB int
	)

	// Check for a minimally viable lead unary operator at depth 0.
	if lenS = len(prs.syms); 1 < lenS && prs.deps[0] == 0 && slices.Contains(UnaryOps, prs.syms[0]) {
		unop = prs.syms[0]
	} else if 2 < lenS && prs.deps[0] == 0 && prs.deps[1] == 0 &&
		(slices.Contains(PredVars, Predicate(prs.syms[1])) ||
			slices.Contains(ArgVars, Argument(prs.syms[1]))) {
		unop = prs.syms[0]
	}

	// Check for a minimally viable binary operator at depth 0.
	if 2 < lenS {
		for dexS, sym = range prs.syms {
			if prs.deps[dexS] != 0 {
				continue
			}

			switch sym {
			case Wedge, Vee, To, Iff:
				dexesB = append(dexesB, dexS)

				lenB += 1
			}

			if lenB == 2 {
				break
			}
		}

		if lenB == 1 {
			dexS = dexesB[0]

			binop = prs.syms[dexS]
		}
	}

	// Decide which, of any, found operators is the main operator,
	// or establish that the formula is ill-formed.
	switch {
	case 1 < lenB: // There are two binary operators at depth 0.
		mop, dexM, ok = NoSymbol, -1, false
	case binop != 0: // There is a binary operator at depth 0.
		mop, dexM, ok = binop, dexS, true // dexS is still dexesB[0].
	case unop != 0: // There is a unary operator.
		mop, dexM, ok = unop, 0, true
	default: // There is no unary or binary operator at depth 0.
		mop, dexM = NoSymbol, -1

		ok = rexBase.MatchString(prs.s) ||
			rexTorF.MatchString(prs.s) ||
			rexIden.MatchString(prs.s)
	}

	return
}

func cutParser(prs *parser) (mop Symbol, pv Predicate, av Argument, prsL, prsR *parser, ok bool) {
	var (
		dex      int
		okL, okR bool
	)

	if rexBase.MatchString(prs.s) || rexTorF.MatchString(prs.s) || rexIden.MatchString(prs.s) {
		// There is no cutting an atomic formula.
		mop, prsL, prsR, ok = NoSymbol, prs, nil, true
	} else if mop, dex, ok = findMainOperator(prs); !ok {
		mop, prsL, prsR, ok = NoSymbol, nil, nil, false
	} else {
		switch mop {
		case Neg, Box, Diamond:
			prsL, okL = newParser(string(prs.syms[1:]))

			okR = true
		case Wedge, Vee, To, Iff:
			prsL, okL = newParser(string(prs.syms[:dex]))

			prsR, okR = newParser(string(prs.syms[dex+1:]))
		case Exists, ForAll:
			if slices.Contains(PredVars, Predicate(prs.syms[1])) {
				pv = Predicate(prs.syms[1])
			}

			if slices.Contains(ArgVars, Argument(prs.syms[1])) {
				av = Argument(prs.syms[1])
			}

			prsL, okL = newParser(string(prs.syms[2:]))

			okR = true
		default:
			panic("Invalid main operator.")
		}

		ok = okL && okR
	}

	return
}

func parseAtomicFmla(prs *parser) (wff *WffTree) {
	var (
		pred       Predicate
		args       []Argument
		argL, argR Argument
		lenS, dex  int
	)

	switch {
	case rexTorF.MatchString(prs.s): // Top or bottom.
		pred = Predicate(prs.syms[0])

		wff = NewAtomicWff(pred)
	case rexIden.MatchString(prs.s): // Identity predicate.
		if lenS = len(prs.syms); lenS != 3 {
			panic("An identity predicate must have exactly three characters.")
		}

		pred = Predicate(prs.syms[1])

		argL, argR = Argument(prs.syms[0]), Argument(prs.syms[2])

		wff = NewAtomicWff(pred, argL, argR)
	case rexBase.MatchString(prs.s): // Base atomic predicate.
		pred = Predicate(prs.syms[0])

		if lenS = len(prs.syms); 1 < lenS {
			args = make([]Argument, lenS-1)

			for dex = 1; dex < lenS; dex += 1 {
				argR = Argument(prs.syms[dex])

				args[dex-1] = argR
			}
		}

		wff = NewAtomicWff(pred, args...)
	default:
		panic("An approved cut led to an illegal atomic formula.")
	}

	return
}

func isClosedWff(wff *WffTree) (is bool) {
	var (
		pvs        []Predicate
		avs        []Argument
		lenP, lenA int
	)

	pvs, avs = GetFreeVariables(wff)

	lenP, lenA = len(pvs), len(avs)

	is = lenP+lenA == 0

	return
}

func parseFullFmla(s string) (fmla *WffTree, ok bool) {
	var (
		prs        *parser
		mop        Symbol
		pv         Predicate
		av         Argument
		prsL, prsR *parser
		subL, subR *WffTree
		okL, okR   bool
	)

	if s, ok = convertNotation(s); ok {
		if prs, ok = newParser(s); ok {
			if mop, pv, av, prsL, prsR, ok = cutParser(prs); ok {
				switch mop {
				case NoSymbol:
					fmla = parseAtomicFmla(prs)

					ok = fmla != nil
				case Neg, Box, Diamond:
					subL, okL = parseFullFmla(prsL.s)

					if ok = okL; ok {
						fmla = NewCompositeWff(mop, subL, nil, 0, 0)
					}
				case Wedge, Vee, To, Iff:
					subL, okL = parseFullFmla(prsL.s)

					subR, okR = parseFullFmla(prsR.s)

					if ok = okL && okR; ok {
						fmla = NewCompositeWff(mop, subL, subR, 0, 0)
					}
				case Exists, ForAll:
					subL, okL = parseFullFmla(prsL.s)

					if ok = okL; ok {
						fmla = NewCompositeWff(mop, subL, nil, pv, av)
					}
				default:
					panic("Invalid main operator.")
				}
			}
		}
	}

	return
}

func ParseStringToWff(s string) (wff *WffTree, ok bool) {
	var (
		fmla *WffTree
	)

	fmla, ok = parseFullFmla(s)

	if ok = ok && isClosedWff(fmla); ok {
		wff = fmla
	} else {
		wff = nil
	}

	return
}
