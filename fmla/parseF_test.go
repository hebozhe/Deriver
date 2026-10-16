package fmla_test

import (
	"Deriver/fmla"
	"testing"
)

type parseTestCase struct {
	name   string
	input  string
	output string
	want   bool
}

var parseTestCases = []parseTestCase{
	{"Empty Input", "", "", false},
	{"Mere Spaces", "    ", "", false},
	{"Empty Parentheses", "()", "", false},

	{"Atomic Input", "A", "A", true},
	{"Atomic Input with Spaces", "   A  ", "A", true},
	{"Atomic Input with Extra Parentheses", "[(({A}))]", "A", true},
	{"Atomic Input with Imbalanced Left Parenthses", "((A)", "", false},
	{"Atomic Input with Imbalanced Right Parentheses", "(A))", "", false},

	{"Unary Input", "[]~<>A", "□¬◇A", true},
	{"Unary Input without Operand", "¬□", "", false},

	{"Binary Input", "(A\\/(B/\\C))->(D<->E)", "(A∨(B∧C))→(D↔E)", true},
	{"Binary Input with Ambiguous Scoping", "A∨B∧C", "", false},
	{"Binary Input without Right Operand", "A∧", "", false},
	{"Binary Input without Left Operand", "∧B", "", false},

	{"Equality Input", "a=b", "a=b", true},
	{"Equality Input in Polish Notation", "=ab", "", false},
	{"Equality Input without Right Operand", "a=", "", false},
	{"Equality Input without Left Operand", "=b", "", false},

	{"Predicate Input", "Abc", "Abc", true},
	{"Predicate Input in Wrong Order", "bAc", "", false},
	{"Predicate Input with Wrong Argument Tuple", "Ab⊥c", "", false},

	{"Quantified Input (2nd Order)", "∀UU", "∀UU", true},
	{"Quantified Input with Wrong Binding (2nd Order)", "∀AA", "", false},
	{"Quantified Input with Open/Free Variable (2nd Order)", "∀U(U→V)", "", false},

	{"Quantified Input (1st Order)", "∀uAu", "∀uAu", true},
	{"Quantified Input with Wrong Binding (1st Order)", "∀aAa", "", false},
	{"Quantified Input with Open/Free Variable (1st Order)", "∀uAuv", "", false},
}

func TestParseWff(t *testing.T) {
	var (
		ptc parseTestCase
	)

	for _, ptc = range parseTestCases {
		t.Run(ptc.name, func(t *testing.T) {
			var (
				wff *fmla.Wff
				s   string
				ok  bool
			)

			if wff, ok = fmla.ParseWff(ptc.input); ok != ptc.want {
				t.Fatalf("ParseWff() = %v for input %q, want %v.", ok, ptc.input, ptc.want)
			} else if ok {
				if s = wff.String(); ptc.want && s != ptc.output {
					t.Fatalf("ParseWff().String() = %q for input %q, want %q.", s, ptc.input, ptc.output)
				}
			}
		})
	}
}

func TestMustParseWff(t *testing.T) {
	var (
		ptc parseTestCase
	)

	for _, ptc = range parseTestCases {
		t.Run(ptc.name, func(t *testing.T) {
			var (
				rec any
			)

			switch ptc.want {
			case true:
				defer func() {
					if rec = recover(); rec != nil {
						t.Fatalf("MustParseWff() = %v for input %q, want %v.", rec, ptc.input, ptc.want)
					}
				}()
			case false:
				defer func() {
					if rec = recover(); rec == nil {
						t.Fatalf("MustParseWff() = %v for input %q, want %v.", rec, ptc.input, ptc.want)
					}
				}()
			}

			_ = fmla.MustParseWff(ptc.input)
		})
	}
}
