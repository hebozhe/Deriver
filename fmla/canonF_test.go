package fmla_test

import (
	"Deriver/fmla"
	"testing"
)

type canonTestCase struct {
	name        string
	input       string
	isCanonical bool
	canon       string
}

var canonTestCases = []canonTestCase{
	{"Canonical Special Atom", "⊤", true, "⊤"},
	{"Canonical Equality Proposition", "a=b", true, "a=b"},
	{"Noncanonical Inequality Proposition", "b=a", false, "a=b"},
	{"Canonical Nonary Predicate", "A", true, "A"},
	{"Noncanonical Nonary Predicate", "B", false, "A"},
	{"Canonical Unary Predicate", "Aa", true, "Aa"},
	{"Noncanonical Unary Predicate", "Ab", false, "Aa"},
	{"Canonical Binary Predicate", "Aab", true, "Aab"},
	{"Noncanonical Binary Predicate", "Abc", false, "Aab"},
	{"Canonical Unary WFF", "¬A", true, "¬A"},
	{"Noncanonical Unary WFF", "¬B", false, "¬A"},
	{"Canonical Binary WFF", "A∧B", true, "A∧B"},
	{"Noncanonical Binary WFF", "B∧C", false, "A∧B"},
	{"Canonical Quantified WFF (2nd Order)", "∀UU", true, "∀UU"},
	{"Noncanonical Quantified WFF (2nd Order)", "∀VV", false, "∀UU"},
	{"Canonical Quantified WFF (1st Order)", "∀uAu", true, "∀uAu"},
	{"Noncanonical Quantified WFF (1st Order)", "∀vAv", false, "∀uAu"},
	{"Noncanonical Composite WFF with Repeated Predicate", "B→B", false, "A→A"},
	{"Noncanonical Composite WFF with Repeated Argument", "Ab→Ab", false, "Aa→Aa"},
	{"Noncanonical Composite WFF with Nested Quantifiers (1st Order)", "∀v∃wAvw", false, "∀u∃vAuv"},
	{"Noncanonical Composite WFF with Interior Quantifiers (1st Order)", "∀v(Av∨∃vAv)", false, "∀u(Au∨∃uAu)"},
}

func TestIsCanonical(t *testing.T) {
	var (
		ctc canonTestCase
	)

	for _, ctc = range canonTestCases {
		t.Run(ctc.name, func(t *testing.T) {
			var (
				wff *fmla.Wff
				is  bool
			)

			wff = fmla.MustParseWff(ctc.input)

			is = wff.IsCanonical()

			if is != ctc.isCanonical {
				t.Fatalf("IsCanonical() = %v, want %v for input %q.", is, ctc.isCanonical, ctc.input)
			}
		})
	}
}

func TestMakeCanonical(t *testing.T) {
	var (
		ctc canonTestCase
	)

	for _, ctc = range canonTestCases {
		t.Run(ctc.name+", Made Canonical", func(t *testing.T) {
			var (
				wffA, wffB *fmla.Wff
			)

			if !ctc.isCanonical {
				wffA = fmla.MustParseWff(ctc.input)

				wffB = wffA.MakeCanonical()

				if !wffB.IsCanonical() {
					t.Fatalf("MakeCanonical() = %q, want %q for input %q.", wffB.String(), ctc.canon, ctc.input)
				}

				if wffB.String() != ctc.canon {
					t.Fatalf("MakeCanonical() = %q, want %q for input %q.", wffB.String(), ctc.canon, ctc.input)
				}
			}
		})
	}
}

func TestCanonPanics(t *testing.T) {
	t.Run("IsCanonical Nil Panic", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic when calling IsCanonical on nil Wff.")
			}
		}()

		wff.IsCanonical()
	})

	t.Run("MakeCanonical Nil Panic", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic when calling MakeCanonical on nil Wff.")
			}
		}()

		wff.MakeCanonical()
	})

	t.Run("IsCanonical Unsupported Kind Panic", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic when calling IsCanonical on Wff with unsupported kind.")
			} else if rec != "Unsupported formula kind." {
				t.Fatalf("Expected panic %q, got %q.", "Unsupported formula kind.", rec)
			}
		}()

		// Because WffKind starts at iota + 1 (Atomic = 1)[cite: 28], a zero-valued Wff struct will have a kind of 0,
		// This safely triggers the default switch case panic[cite: 27, 28].
		wff = new(fmla.Wff)

		_ = wff.IsCanonical()
	})

	t.Run("MakeCanonical Unsupported Kind Panic", func(t *testing.T) {
		var wff *fmla.Wff

		defer func() {
			var rec any

			if rec = recover(); rec == nil {
				t.Fatal("Expected panic when calling MakeCanonical on Wff with unsupported kind.")
			} else if rec != "Unsupported formula kind." {
				t.Fatalf("Expected panic %q, got %q.", "Unsupported formula kind.", rec)
			}
		}()

		wff = new(fmla.Wff)

		_ = wff.MakeCanonical()
	})
}
