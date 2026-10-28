package nd_test

import (
	"Deriver/fmla"
	"Deriver/nd"
	"Deriver/nd/pr"
	"context"
	"fmt"
	"testing"
	"time"
)

func ndTestParseWff(t *testing.T, s string) (wff *fmla.Wff) {
	var ok bool

	t.Helper()

	if wff, ok = fmla.ParseWff(s); !ok {
		t.Fatalf("Failed to parse %q.", s)
	}

	return
}

func ndTestParseWffs(t *testing.T, ss ...string) (wffs []*fmla.Wff) {
	var (
		s   string
		wff *fmla.Wff
		ok  bool
	)

	t.Helper()

	for _, s = range ss {
		if wff, ok = fmla.ParseWff(s); !ok {
			t.Fatalf("Failed to parse %q.", s)
		}

		wffs = append(wffs, wff)
	}

	return
}

type testCase struct {
	prems []string
	goal  string
	inf   pr.InfSt
	mod   pr.ModSt
	title string
	numD  int // The number of derivations expected from DeriveWeakest.
}

var testCases []testCase = []testCase{
	// Simple Rule Application
	{nil, "⊤", pr.Implicational, pr.NoModality, "⊤I", 1},
	{[]string{"A→B", "A"}, "B", pr.Implicational, pr.NoModality, "→E", 1},
	{[]string{"A→B", "B→C"}, "A→C", pr.Implicational, pr.NoModality, "→I", 1},
	{[]string{"A"}, "B→A", pr.Implicational, pr.NoModality, "Reit", 1},
	{[]string{"A", "B"}, "A∧B", pr.Positive, pr.NoModality, "∧I", 1},
	{[]string{"A∧B"}, "A", pr.Positive, pr.NoModality, "∧E(L)", 1},
	{[]string{"A∧B"}, "B", pr.Positive, pr.NoModality, "∧E(R)", 1},
	{[]string{"A"}, "A∨B", pr.Positive, pr.NoModality, "∨I(L)", 1},
	{[]string{"A"}, "B∨A", pr.Positive, pr.NoModality, "∨I(R)", 1},
	{[]string{"A∨B", "A→C", "B→C"}, "C", pr.Positive, pr.NoModality, "∨E", 1},
	{[]string{"A→B", "B→A"}, "A↔B", pr.Positive, pr.NoModality, "↔I", 1},
	{[]string{"A↔B"}, "A→B", pr.Positive, pr.NoModality, "↔E(L)", 1},
	{[]string{"A↔B"}, "B→A", pr.Positive, pr.NoModality, "↔E(R)", 1},
	{[]string{"A", "¬A"}, "⊥", pr.Minimal, pr.NoModality, "⊥I", 1},
	{[]string{"A→⊥"}, "¬A", pr.Intuitionistic, pr.NoModality, "¬I", 1},
	{[]string{"⊥"}, "A", pr.Intuitionistic, pr.NoModality, "⊥E", 1},
	{[]string{"¬A→B", "¬¬A→B"}, "B", pr.Jankov, pr.NoModality, "Jan", 1},
	{[]string{"(A→B)→C", "(B→A)→C"}, "C", pr.GödelDummett, pr.NoModality, "Göd", 1},
	{[]string{"A→C", "¬B→C", "(A→B)→C"}, "C", pr.Smetanich, pr.NoModality, "Sme", 1},
	{[]string{"¬¬A"}, "A", pr.Classical, pr.NoModality, "¬E", 1},
	{nil, "a=a", pr.Implicational, pr.NoModality, "=I", 1},
	{[]string{"a=b", "Aaa"}, "Aba", pr.Implicational, pr.NoModality, "=E(1L)", 1},
	{[]string{"a=b", "Aaa"}, "Aab", pr.Implicational, pr.NoModality, "=E(1R)", 1},
	{[]string{"a=b", "Aaa"}, "Abb", pr.Implicational, pr.NoModality, "=E(All)", 1},
	{[]string{"∀uAuau"}, "Aaaa∧Abab", pr.Positive, pr.NoModality, "∀E(1QL)", 1},
	{nil, "∀u(A→A)", pr.Positive, pr.NoModality, "∀I(1QL)(0-ary)", 1},
	{nil, "∀u(Au→Au)", pr.Positive, pr.NoModality, "∀I(1QL)(n-ary)", 1},
	{[]string{"∀u∀vAuv"}, "∀v∀uAvu", pr.Positive, pr.NoModality, "∀I(1QL)(Swap)", 1},
	{[]string{"∀u∀vAuv"}, "∀v∀uAuv", pr.Positive, pr.NoModality, "∀I(1QL)(Move)", 1},
	{[]string{"∀UUa"}, "Aa∧Ba", pr.Positive, pr.NoModality, "∀E(2QL)", 1},
	{nil, "∀U(A→A)", pr.Positive, pr.NoModality, "∀I(2QL)(0-ary)", 1},
	{nil, "∀U(Ua→Ua)", pr.Positive, pr.NoModality, "∀I(2QL)(n-ary)", 1},
	{[]string{"∀U∀V(Ua∨Vb)"}, "∀V∀U(Va∨Ub)", pr.Positive, pr.NoModality, "∀I(2QL)(Swap)", 1},
	{[]string{"∀U∀V(Ua∨Vb)"}, "∀V∀U(Ua∨Vb)", pr.Positive, pr.NoModality, "∀I(2QL)(Move)", 1},
	{nil, "∃u⊤", pr.Positive, pr.NoModality, "∃I(1QL)(0-ary)", 1},
	{[]string{"Aaa"}, "∃uAua", pr.Positive, pr.NoModality, "∃I(IQL)(1L)", 1},
	{[]string{"Aaa"}, "∃uAau", pr.Positive, pr.NoModality, "∃I(IQL)(1R)", 1},
	{[]string{"Aaa"}, "∃uAuu", pr.Positive, pr.NoModality, "∃I(IQL)(All)", 1},
	{[]string{"∃uA"}, "A", pr.Positive, pr.NoModality, "∃E(1QL)(0-ary)", 1},
	{[]string{"∃u((u=u)→Aab)"}, "Aab", pr.Positive, pr.NoModality, "∃E(1QL)(n-ary)", 1},
	{[]string{"∃u∃vAuv"}, "∃v∃uAvu", pr.Positive, pr.NoModality, "∃E(1QL)(Swap)", 1},
	{[]string{"∃u∃vAuv"}, "∃v∃uAuv", pr.Positive, pr.NoModality, "∃E(1QL)(Move)", 1},
	{nil, "∃U⊤", pr.Positive, pr.NoModality, "∃I(2QL)(0-ary)", 1},
	{[]string{"Aa→Aa"}, "∃U(Ua→Aa)", pr.Positive, pr.NoModality, "∃I(2QL)(1L)", 1},
	{[]string{"Aa→Aa"}, "∃U(Aa→Ua)", pr.Positive, pr.NoModality, "∃I(2QL)(1R)", 1},
	{[]string{"Aa→Aa"}, "∃U(Ua→Ua)", pr.Positive, pr.NoModality, "∃I(2QL)(All)", 1},
	{[]string{"∃UA"}, "A", pr.Positive, pr.NoModality, "∃E(2QL)(0-ary)", 1},
	{[]string{"∃U((U→U)→A)"}, "A", pr.Positive, pr.NoModality, "∃E(2QL)(n-ary)", 1},
	{[]string{"∃U∃V(Ua∨Va)"}, "∃V∃U(Va∨Ua)", pr.Positive, pr.NoModality, "∃E(1QL)(Swap)", 1},
	{[]string{"∃U∃V(Ua∨Va)"}, "∃V∃U(Ua∨Va)", pr.Positive, pr.NoModality, "∃E(1QL)(Move)", 1},
	{nil, "□(A∨B)→□(B∨A)", pr.Positive, pr.ModalEw, "□Con", 1},
	{nil, "◇(A∨B)→◇(B∨A)", pr.Positive, pr.ModalEw, "◇Con", 1},
	{[]string{"□⊤", "□⊥"}, "¬◇⊥∧¬◇⊤", pr.Minimal, pr.ModalEw, "□Ew", 1},
	{[]string{"◇⊤", "◇⊥"}, "¬□⊥∧¬□⊤", pr.Minimal, pr.ModalEw, "◇Ew", 1},
	{[]string{"¬□¬A"}, "◇A", pr.Classical, pr.ModalEw, "◇I", 1},
	{[]string{"□A", "□¬B"}, "¬◇¬A∧¬◇B", pr.Minimal, pr.ModalEn, "□En", 1},
	{[]string{"◇A", "◇¬B"}, "¬□¬A∧¬□B", pr.Minimal, pr.ModalEn, "◇En", 1},
	{[]string{"□A"}, "¬◇(B∧¬B)", pr.Minimal, pr.ModalEs, "□Es", 1},
	{[]string{"◇A"}, "¬□(B∧¬B)", pr.Minimal, pr.ModalEs, "◇Es", 1},
	{nil, "□A→□(A∨B)", pr.Positive, pr.ModalM, "□Mon", 1},
	{nil, "◇A→◇(A∨B)", pr.Positive, pr.ModalM, "◇Mon", 1},
	{[]string{"□(A∧B)"}, "□A∧□B", pr.Positive, pr.ModalM, "□E", 1},
	{[]string{"◇A"}, "◇(A∨B)", pr.Positive, pr.ModalM, "◇E", 1},
	{nil, "□(A→(A∨B))", pr.Positive, pr.ModalN, "□I", 1},
	{nil, "¬◇⊥", pr.Minimal, pr.ModalN, "¬◇I", 1},
	{[]string{"□A", "□B"}, "□(A∧B)", pr.Positive, pr.ModalC, "□Agg", 1},
	{[]string{"□A", "□(A→B)"}, "□B", pr.Positive, pr.ModalM * pr.ModalC, "Reit[C]", 1},
	{[]string{"◇A", "□(A→B)"}, "◇B", pr.Positive, pr.ModalK, "Reit[K]", 1},
	{[]string{"□A"}, "◇A", pr.Positive, pr.ModalD, "D", 1},
	{[]string{"A"}, "◇A", pr.Positive, pr.ModalT, "TI", 1},
	{[]string{"□A"}, "A", pr.Positive, pr.ModalT, "TE", 1},
	{[]string{"□A"}, "□□A", pr.Positive, pr.Modal4, "4I", 1},
	{[]string{"◇◇A"}, "◇A", pr.Positive, pr.Modal4, "4E", 1},
	{[]string{"A"}, "□◇A", pr.Positive, pr.ModalB, "BI", 1},
	{[]string{"◇□A"}, "A", pr.Positive, pr.ModalB, "BE", 1},
	{[]string{"◇A"}, "□◇A", pr.Positive, pr.Modal5, "5I", 1},
	{[]string{"◇□A"}, "□A", pr.Positive, pr.Modal5, "5E", 1},

	// Axiomatizations, Theorems, Distributions, and Reductions
	{nil, "A→A", pr.Implicational, pr.NoModality, "Identity", 1},
	{nil, "A→(B→A)", pr.Implicational, pr.NoModality, "Weakening", 1},
	{nil, "(A→(A→B))→(A→B)", pr.Implicational, pr.NoModality, "Contraction", 1},
	{nil, "(A→(B→C))→(B→(A→C))", pr.Implicational, pr.NoModality, "Permutation", 1},
	{nil, "(A→B)→((B→C)→(A→C))", pr.Implicational, pr.NoModality, "Hyp Syll(LR)", 1},
	{nil, "(A→B)→((C→A)→(C→B))", pr.Implicational, pr.NoModality, "Hyp Syll(RL)", 1},
	{nil, "(A→(B→C))→((A→B)→(A→C))", pr.Implicational, pr.NoModality, "Frege 2", 1},
	{nil, "(A→B)→((A→(B→C))→(A→C))", pr.Implicational, pr.NoModality, "Meredith 2", 1},
	{nil, "A→((B→C)→(((D→B)→(C→E))→(B→E)))", pr.Implicational, pr.NoModality, "Meredith 1", 1},
	{nil, "((A→B)→C)→(D→((B→(C→E))→(B→E)))", pr.Implicational, pr.NoModality, "Meredith 3", 1},

	{nil, "A→¬¬A", pr.Minimal, pr.NoModality, "DNI", 1},
	{nil, "¬(A∧¬A)", pr.Minimal, pr.NoModality, "LNC ∧", 1},
	{nil, "¬(A↔¬A)", pr.Minimal, pr.NoModality, "LNC ↔", 1},
	{nil, "¬¬¬A→¬A", pr.Minimal, pr.NoModality, "¬¬ (Min)", 1},
	{nil, "(A→¬A)→¬A", pr.Minimal, pr.NoModality, "RAA ¬", 1},
	{nil, "(¬A→A)→¬¬A", pr.Minimal, pr.NoModality, "RAA ¬¬", 1},
	{nil, "(A→¬B)→(B→¬A)", pr.Minimal, pr.NoModality, "Antitone →", 1},
	{nil, "(A→B)→(¬B→¬A)", pr.Minimal, pr.NoModality, "Modus Tollens", 1},
	{nil, "¬(A∧B)→(A→¬B)", pr.Minimal, pr.NoModality, "¬∧ (Min)(LR)", 1},
	{nil, "¬(A∧B)→(B→¬A)", pr.Minimal, pr.NoModality, "¬∧ (Min)(RL)", 1},
	{nil, "¬¬(A∨B)→(¬A→¬¬B)", pr.Jankov, pr.NoModality, "¬¬∨ (Min)(LR)", 1},
	{nil, "¬¬(A∨B)→(¬B→¬¬A)", pr.Jankov, pr.NoModality, "¬¬∨ (Min)(RL)", 1},
	{nil, "(¬¬A→¬¬B)→(¬B→¬A)", pr.Minimal, pr.NoModality, "Contra (Min)", 1},

	{nil, "¬A→(A→B)", pr.Intuitionistic, pr.NoModality, "Explosion", 1},

	{nil, "¬A∨¬¬A", pr.Jankov, pr.NoModality, "WLEM ∨", 1},
	{nil, "¬¬A∨¬¬¬A", pr.Jankov, pr.NoModality, "WLEM ¬", 1},
	{nil, "(A→¬A)∨(¬A→A)", pr.Jankov, pr.NoModality, "WLIN", 1},
	{nil, "(A→B)∨(¬A→¬B)", pr.Jankov, pr.NoModality, "WDGP", 1},
	{nil, "(A→B)→(¬A∨¬¬B)", pr.Jankov, pr.NoModality, "→ (Jan)", 1},
	{nil, "¬(A∧B)→(¬A∨¬B)", pr.Jankov, pr.NoModality, "¬∧ (Jan)", 1},
	{nil, "(¬¬A→A)→(A∨¬A)", pr.Jankov, pr.NoModality, "Limited LEM", 1},
	{nil, "¬¬(A∨B)→(¬¬A∨¬¬B)", pr.Jankov, pr.NoModality, "¬¬∨ (Jan)", 1},
	{nil, "(A→(B∨¬C))→((A→B)∨(A→¬C))", pr.Jankov, pr.NoModality, "NIP", 1},
	{nil, "(¬A→(B→C))→((B→(¬¬A→C))→(B→C))", pr.Jankov, pr.NoModality, "Jan Permutes", 1},

	{nil, "(A→B)∨(B→A)", pr.GödelDummett, pr.NoModality, "LIN/DGP", 1},
	{nil, "(((A→B)→B)∧((B→A)→A))→(A∨B)", pr.GödelDummett, pr.NoModality, "∨/→ Correspondence", 1},

	{nil, "(¬A∨B)∨(B→A)", pr.Smetanich, pr.NoModality, "Hosoi 1", 1},
	{nil, "¬A∨(B∨(B→A))", pr.Smetanich, pr.NoModality, "Hosoi 2", 1},
	{nil, "A∨(¬B∨(A→B))", pr.Smetanich, pr.NoModality, "Hosoi 3", 1},
	{nil, "(¬A→B)→(((B→A)→B)→B)", pr.Smetanich, pr.NoModality, "Smetanich", 1},

	{nil, "A∨¬A", pr.Classical, pr.NoModality, "LEM", 1},
	{nil, "¬¬A→A", pr.Classical, pr.NoModality, "¬¬ (Cls)", 1},
	{nil, "((A→B)→A)→A", pr.Classical, pr.NoModality, "Peirce", 1},
	{nil, "(¬A→¬B)→(B→A)", pr.Classical, pr.NoModality, "Contra (Cls)", 1},
}

func TestDeriveAtStrength(t *testing.T) {
	var (
		deadline time.Time
		ok, pass bool
		ctx      context.Context
		cancel   context.CancelFunc
		tc       testCase
		drv      *nd.Drv
	)

	// Get the suite's absolute deadline if provided via -timeout.
	if deadline, ok = t.Deadline(); !ok {
		deadline = time.Now().Add(10 * time.Second)
	}

	ctx, cancel = context.WithDeadline(context.Background(), deadline.Add(-1*time.Second))

	defer cancel()

	for _, tc = range testCases {
		drv = nd.NewDeriver(tc.inf, tc.mod, ndTestParseWff(t, tc.goal), ndTestParseWffs(t, tc.prems...)...)

		pass = t.Run(fmt.Sprintf("%s from %s (%s)", tc.goal, tc.prems, tc.title), func(t *testing.T) {
			var (
				done        chan struct{}
				fitch, last string
			)

			// Channel to signal that processing completed successfully.
			done = make(chan struct{})

			// Move the long-running operation into a separate goroutine.
			go func() {
				defer close(done)

				if !drv.DeriveAtStrength() {
					t.Errorf("Derivation of %q from %q failed.", tc.goal, tc.prems)
				}
			}()

			select {
			case <-done: // The derivation completed successfully.
				fitch = drv.Prf.FitchFormat()

				t.Logf("\nCompleted:\n%s\n", fitch)

				_ = drv.Prf.Prune()

				fitch = drv.Prf.FitchFormat()

				t.Logf("\nPruned:\n%s\n", fitch)
			case <-ctx.Done(): // The user time expired.
				last = drv.Prf.FitchFormat()

				println("\n--- TEST TIMEOUT INTERRUPT ---")
				println("Failed TestCase Name:", tc.title)
				println("Proof Current State:\n", last)
				println("------------------------------")

				t.Fatalf("Test timed out during %s", tc.title)
			}
		})

		if !pass {
			break
		}
	}
}
