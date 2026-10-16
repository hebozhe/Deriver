package fmla

import (
	"fmt"
	"slices"
	"strings"
	"unicode"
)

type convStruct struct {
	from string
	into string
}

func newConv[T Symbol | Predicate](from string, to T) (cs convStruct) {
	cs = convStruct{from: from, into: string(to)}

	return
}

var convs = []convStruct{
	// Three-character transformations:
	newConv("<->", Iff),
	// Two-character transformations:
	newConv("->", To),
	newConv("\\/", Vee),
	newConv("/\\", Wedge),
	newConv("[]", Box),
	newConv("<>", Dmd),
	// One-character transformations:
	newConv("~", Neg),
	newConv("$", Exists),
	newConv("@", ForAll),
	newConv("^", Top),
	newConv("#", Bot),
	newConv("{", LPar),
	newConv("}", RPar),
	newConv("[", LPar),
	newConv("]", RPar),
}

func convertNotation(sA string) (sB string) {
	var (
		cs convStruct
	)

	sB = strings.Map(func(r rune) (s rune) {
		if unicode.IsSpace(r) {
			s = -1
		} else {
			s = r
		}

		return
	}, sA)

	for _, cs = range convs {
		sB = strings.ReplaceAll(sB, cs.from, cs.into)
	}

	return
}

type parseTree struct {
	base string
	kind WffKind
	atom *Wff
	ptL  *parseTree
	ptR  *parseTree
}

func calcDepths(s string) (rs []rune, deps []int) {
	var (
		lenR, dex, last int
		r               rune
	)

	if s != "" {
		rs = []rune(s)

		if lenR = len(rs); 0 < lenR {
			deps = make([]int, lenR)

			for dex, r = range rs {
				switch r {
				case rune(LPar):
					deps[dex], last = last+1, last+1
				case rune(RPar):
					deps[dex], last = last-1, last-1
				default:
					deps[dex] = last
				}

				if last < 0 { // Unbalanced with too many closed parentheses.
					rs, deps = nil, nil

					break
				}
			}
		}

		if rs != nil && deps != nil {
			if 0 < deps[lenR-1] { // Unbalanced with too many open parentheses.
				rs, deps = nil, nil
			} else if slices.Index(deps, 0) == lenR-1 && rs[lenR-1] == rune(RPar) { // Balanced, but surrounded by parentheses.
				s = string(rs[1 : lenR-1])

				rs, deps = calcDepths(s)
			}
		}
	}

	return
}

func buildParseTree(s string) (pt *parseTree) {
	var (
		rs             []rune
		deps           []int
		dex, lenX, sel int
		r              rune
		args           []Argument
	)

	if rs, deps = calcDepths(s); rs != nil {
		// First, check for binary formulae.
		for dex, r = range rs {
			// Here, lenX is the number of binary operators at the same depth.
			if deps[dex] == 0 && slices.Contains(BinaryOps, Symbol(r)) {
				lenX, sel = lenX+1, dex
			}
		}

		switch lenX {
		case 0: // Do nothing. Move on.
		case 1:
			pt = &parseTree{
				base: string(rs[sel]),
				kind: Binary,
				atom: nil,
				ptL:  buildParseTree(string(rs[:sel])),
				ptR:  buildParseTree(string(rs[sel+1:])),
			}

			goto BUILDPARSETREE_VALIDATE
		default: // Too many binary operators at the same depth.
			goto BUILDPARSETREE_VALIDATE
		}

		lenX = len(rs)

		// Next, check for unary formulae.
		if 0 < lenX && deps[0] == 0 && slices.Contains(UnaryOps, Symbol(rs[0])) {
			pt = &parseTree{
				base: string(rs[0]),
				kind: Unary,
				atom: nil,
				ptL:  buildParseTree(string(rs[1:])),
				ptR:  nil,
			}

			goto BUILDPARSETREE_VALIDATE
		}

		// Next, check for quantified formulae.
		if 2 < lenX && deps[0] == 0 && deps[1] == 0 && slices.Contains(Quantifiers, Symbol(rs[0])) {
			if slices.Contains(PredVars, Predicate(rs[1])) {
				pt = &parseTree{
					base: fmt.Sprintf("%c%c", rs[0], rs[1]),
					kind: Quantified,
					atom: nil,
					ptL:  buildParseTree(string(rs[2:])),
					ptR:  nil,
				}

				goto BUILDPARSETREE_VALIDATE
			} else if slices.Contains(ArgVars, Argument(rs[1])) {
				pt = &parseTree{
					base: fmt.Sprintf("%c%c", rs[0], rs[1]),
					kind: Quantified,
					atom: nil,
					ptL:  buildParseTree(string(rs[2:])),
					ptR:  nil,
				}

				goto BUILDPARSETREE_VALIDATE
			}
		}

		// Finally, check for atomic formulae.
		if !slices.Contains(rs, rune(LPar)) && !slices.Contains(rs, rune(RPar)) { // No more parentheses.
			switch lenX {
			case 1: // Has to be a predicate.
				if slices.Contains(Preds, Predicate(rs[0])) && Predicate(rs[0]) != Equal {
					pt = &parseTree{
						base: "",
						kind: Atomic,
						atom: NewAtomicWff(Predicate(rs[0])),
						ptL:  nil,
						ptR:  nil,
					}

					goto BUILDPARSETREE_VALIDATE
				}
			case 3: // Potentially of the form '<arg>=<arg>'.
				if Predicate(rs[1]) == Equal {
					if slices.Contains(Args, Argument(rs[0])) && slices.Contains(Args, Argument(rs[2])) {
						pt = &parseTree{
							base: "",
							kind: Atomic,
							atom: NewAtomicWff(Equal, Argument(rs[0]), Argument(rs[2])),
							ptL:  nil,
							ptR:  nil,
						}

						goto BUILDPARSETREE_VALIDATE
					}
				}

				fallthrough
			default: // 2, or 4 or more... Has to be a predicate head with arguments as its tail.
				if slices.Contains(Preds, Predicate(rs[0])) && !slices.Contains(SpecPredConsts, Predicate(rs[0])) {
					for _, r = range rs[1:] {
						if slices.Contains(Args, Argument(r)) {
							args = append(args, Argument(r))
						} else { // Something in the tail is not an argument.
							goto BUILDPARSETREE_VALIDATE
						}
					}

					pt = &parseTree{
						base: "",
						kind: Atomic,
						atom: NewAtomicWff(Predicate(rs[0]), args...),
						ptL:  nil,
						ptR:  nil,
					}

					goto BUILDPARSETREE_VALIDATE
				}
			}
		}
	}

BUILDPARSETREE_VALIDATE:
	if pt != nil {
		switch pt.kind {
		case Atomic:
			// No validation needed. Atomic nodes always make a valid atom.
		case Unary, Quantified:
			if pt.ptL == nil {
				pt = nil
			}
		case Binary:
			if pt.ptL == nil || pt.ptR == nil {
				pt = nil
			}
		}
	}

	return
}

func (pt *parseTree) buildWff() (fmla *Wff, ok bool) {
	var (
		rs           []rune
		fmlaL, fmlaR *Wff
	)

	switch pt.kind {
	case Atomic:
		fmla, ok = pt.atom, true
	case Unary:
		rs = []rune(pt.base)

		if fmlaL, ok = pt.ptL.buildWff(); ok {
			fmla = NewUnaryWff(Symbol(rs[0]), fmlaL)
		}
	case Binary:
		rs = []rune(pt.base)

		if fmlaL, ok = pt.ptL.buildWff(); ok {
			if fmlaR, ok = pt.ptR.buildWff(); ok {
				fmla = NewBinaryWff(Symbol(rs[0]), fmlaL, fmlaR)
			}
		}
	case Quantified:
		rs = []rune(pt.base)

		if fmlaL, ok = pt.ptL.buildWff(); ok {
			if ok = slices.Contains(PredVars, Predicate(rs[1])); ok {
				fmla = NewQuantifiedWff(Symbol(rs[0]), fmlaL, Predicate(rs[1]), NoArg)
			} else if ok = slices.Contains(ArgVars, Argument(rs[1])); ok {
				fmla = NewQuantifiedWff(Symbol(rs[0]), fmlaL, NoPred, Argument(rs[1]))
			}
		}
	}

	return
}

func ParseWff(s string) (wff *Wff, ok bool) {
	var (
		pt   *parseTree
		fmla *Wff
	)

	s = convertNotation(s)
	pt = buildParseTree(s)

	if ok = pt != nil; ok {
		if fmla, ok = pt.buildWff(); ok {
			if ok = fmla.IsClosed(); ok { // Only accept closed wffs.
				wff = fmla
			}
		}
	}

	return
}

func MustParseWff(s string) (wff *Wff) {
	var (
		ok  bool
		msg string
	)

	if wff, ok = ParseWff(s); !ok {
		msg = fmt.Sprintf("Failed to parse %q.", s)

		panic(msg)
	}

	return
}

func ParseWffFromTemplate(tmp string, wffs ...*Wff) (wff *Wff, ok bool) {
	var (
		lenW int
		s    string
		ins  []any
	)

	if lenW = len(wffs); lenW == strings.Count(tmp, "%s") {
		s = strings.ReplaceAll(tmp, "%s", "(%s)")

		for _, wff = range wffs {
			ins = append(ins, wff.String())
		}

		s = fmt.Sprintf(s, ins...)

		wff, ok = ParseWff(s)
	}

	return
}

func MustParseWffFromTemplate(tmp string, wffs ...*Wff) (wff *Wff) {
	var (
		ok  bool
		msg string
		ss  []string
	)

	if wff, ok = ParseWffFromTemplate(tmp, wffs...); !ok {
		for _, wff = range wffs {
			ss = append(ss, wff.String())
		}

		msg = fmt.Sprintf("Failed to parse template %q with wffs %q.", tmp, ss)

		panic(msg)
	}

	return
}
