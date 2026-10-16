package fmla_test

import (
	"Deriver/fmla"
	"testing"
)

func expectPanic(t *testing.T, expMsg string) {
	var (
		rec any
		msg string
		ok  bool
	)

	if rec = recover(); rec == nil {
		t.Fatalf("Expected panic with message %q, but no panic occurred.", expMsg)
	}

	if msg, ok = rec.(string); !ok || msg != expMsg {
		t.Fatalf("Expected panic message %q, got %v", expMsg, rec)
	}
}

func TestMakeWffPanics(t *testing.T) {
	var wff *fmla.Wff

	wff = fmla.NewAtomicWff(fmla.Predicate('A'))

	t.Run("NewAtomicWff: Equal with 1 or Fewer Arguments", func(t *testing.T) {
		defer expectPanic(t, "Equality predicate requires exactly two arguments.")

		_ = fmla.NewAtomicWff(fmla.Equal, fmla.Argument('a'))
	})

	t.Run("NewAtomicWff: Equal with 3 or More Arguments", func(t *testing.T) {
		defer expectPanic(t, "Equality predicate requires exactly two arguments.")

		_ = fmla.NewAtomicWff(fmla.Equal, []fmla.Argument("abc")...)
	})

	t.Run("NewUnaryWff: Nil Subformula", func(t *testing.T) {
		defer expectPanic(t, "Missing subformula.")

		_ = fmla.NewUnaryWff(fmla.Neg, nil)
	})

	t.Run("NewUnaryWff: Invalid Operator", func(t *testing.T) {
		defer expectPanic(t, "Invalid unary operator.")

		_ = fmla.NewUnaryWff(fmla.Wedge, wff)
	})

	t.Run("NewBinaryWff: Nil Left Subformula", func(t *testing.T) {
		defer expectPanic(t, "Missing subformulae.")

		_ = fmla.NewBinaryWff(fmla.Wedge, nil, wff)
	})

	t.Run("NewBinaryWff: Nil Right Subformula", func(t *testing.T) {
		defer expectPanic(t, "Missing subformulae.")

		_ = fmla.NewBinaryWff(fmla.Wedge, wff, nil)
	})

	t.Run("NewBinaryWff: Invalid Operator", func(t *testing.T) {
		defer expectPanic(t, "Invalid binary operator.")

		_ = fmla.NewBinaryWff(fmla.Neg, wff, wff) // Neg is unary, not binary
	})

	t.Run("NewQuantifiedWff: Nil Subformula", func(t *testing.T) {
		defer expectPanic(t, "Missing subformula.")

		_ = fmla.NewQuantifiedWff(fmla.ForAll, nil, fmla.PredVars[0], fmla.NoArg)
	})

	t.Run("NewQuantifiedWff: Ambiguous Variable", func(t *testing.T) {
		defer expectPanic(t, "Ambiguous variable over which to quantify.")

		_ = fmla.NewQuantifiedWff(fmla.ForAll, wff, fmla.PredVars[0], fmla.ArgVars[0])
	})

	t.Run("NewQuantifiedWff: No Variable", func(t *testing.T) {
		defer expectPanic(t, "No variable over which to quantify.")

		_ = fmla.NewQuantifiedWff(fmla.ForAll, wff, fmla.NoPred, fmla.NoArg)
	})

	t.Run("NewQuantifiedWff: Invalid Predicate Variable", func(t *testing.T) {
		defer expectPanic(t, "Invalid predicate variable.")

		_ = fmla.NewQuantifiedWff(fmla.ForAll, wff, fmla.Predicate('A'), fmla.NoArg)
	})

	t.Run("NewQuantifiedWff: Invalid Argument Variable", func(t *testing.T) {
		defer expectPanic(t, "Invalid argument variable.")

		_ = fmla.NewQuantifiedWff(fmla.ForAll, wff, fmla.NoPred, fmla.Argument('a')) // 'a' is a constant
	})

	t.Run("NewQuantifiedWff: Invalid Quantifier", func(t *testing.T) {
		defer expectPanic(t, "Invalid quantifier.")

		_ = fmla.NewQuantifiedWff(fmla.Wedge, wff, fmla.NoPred, fmla.ArgVars[0])
	})
}
