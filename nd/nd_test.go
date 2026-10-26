package nd_test

import (
	"Deriver/fmla"
	"Deriver/nd"
	"Deriver/nd/pr"
	"context"
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
	title string
	prems []string
	goal  string
	inf   pr.InfSt
	mod   pr.ModSt
	numD  int // The number of derivations expected from DeriveWeakest.
}

var testCases []testCase = []testCase{
	// Simple rule application.
	{"⊤I", nil, "⊤", pr.Implicational, pr.NoModality, 1},
	{"→E", []string{"A→B", "A"}, "B", pr.Implicational, pr.NoModality, 1},
	{"→I", []string{"A→B", "B→C"}, "A→C", pr.Implicational, pr.NoModality, 1},
	{"Reit", []string{"A"}, "B→A", pr.Implicational, pr.NoModality, 1},
	{"∧I", []string{"A", "B"}, "A∧B", pr.Positive, pr.NoModality, 1},
	{"∧E(L)", []string{"A∧B"}, "A", pr.Positive, pr.NoModality, 1},
	{"∧E(R)", []string{"A∧B"}, "B", pr.Positive, pr.NoModality, 1},
	{"∨I(L)", []string{"A"}, "A∨B", pr.Positive, pr.NoModality, 1},
	{"∨I(R)", []string{"A"}, "B∨A", pr.Positive, pr.NoModality, 1},
	{"∨E", []string{"A∨B", "A→C", "B→C"}, "C", pr.Positive, pr.NoModality, 1},
	{"↔I", []string{"A→B", "B→A"}, "A↔B", pr.Positive, pr.NoModality, 1},
	{"↔E(L)", []string{"A↔B", "A"}, "B", pr.Positive, pr.NoModality, 1},
	{"↔E(R)", []string{"A↔B", "B"}, "A", pr.Positive, pr.NoModality, 1},
	{"⊥I", []string{"A", "¬A"}, "⊥", pr.Minimal, pr.NoModality, 1},
	{"¬I", []string{"A→⊥"}, "¬A", pr.Intuitionistic, pr.NoModality, 1},
	{"⊥E", []string{"⊥"}, "A", pr.Intuitionistic, pr.NoModality, 1},
	{"Jan", []string{"¬A→B"}, "¬¬A∨B", pr.Jankov, pr.NoModality, 1},
	{"Göd", []string{"(A→B)→C"}, "(B→A)∨C", pr.GödelDummett, pr.NoModality, 1},
	{"Sme", []string{"(A→B)→C"}, "(A∨¬B)∨C", pr.Smetanich, pr.NoModality, 1},
	{"¬E", []string{"¬¬A"}, "A", pr.Classical, pr.NoModality, 1},
	{"=I", nil, "a=a", pr.Implicational, pr.NoModality, 1},
	{"=E(1L)", []string{"a=b", "Aaa"}, "Aba", pr.Implicational, pr.NoModality, 1},
	{"=E(1R)", []string{"a=b", "Aaa"}, "Aab", pr.Implicational, pr.NoModality, 1},
	{"=E(All)", []string{"a=b", "Aaa"}, "Abb", pr.Implicational, pr.NoModality, 1},
	{"∀E(1QL)", []string{"∀uAuau"}, "Aaaa∧Abab", pr.Positive, pr.NoModality, 1},
	{"∀I(1QL)(0-ary)", nil, "∀u(A→A)", pr.Positive, pr.NoModality, 1},
	{"∀I(1QL)(n-ary)", nil, "∀u(Au→Au)", pr.Positive, pr.NoModality, 1},
	{"∀I(1QL)(Swap)", []string{"∀u∀vAuv"}, "∀v∀uAvu", pr.Positive, pr.NoModality, 1},
	{"∀I(1QL)(Move)", []string{"∀u∀vAuv"}, "∀v∀uAuv", pr.Positive, pr.NoModality, 1},
	{"∀E(2QL)", []string{"∀UUa"}, "Aa∧Ba", pr.Positive, pr.NoModality, 1},
	{"∀I(2QL)(0-ary)", nil, "∀U(A→A)", pr.Positive, pr.NoModality, 1},
	{"∀I(2QL)(n-ary)", nil, "∀U(Ua→Ua)", pr.Positive, pr.NoModality, 1},
	{"∀I(2QL)(Swap)", []string{"∀U∀V(Ua∨Vb)"}, "∀V∀U(Va∨Ub)", pr.Positive, pr.NoModality, 1},
	{"∀I(2QL)(Move)", []string{"∀U∀V(Ua∨Vb)"}, "∀V∀U(Ua∨Vb)", pr.Positive, pr.NoModality, 1},
	{"∃I(1QL)(0-ary)", nil, "∃u⊤", pr.Positive, pr.NoModality, 1},
	{"∃I(IQL)(1L)", []string{"Aaa"}, "∃uAua", pr.Positive, pr.NoModality, 1},
	{"∃I(IQL)(1R)", []string{"Aaa"}, "∃uAau", pr.Positive, pr.NoModality, 1},
	{"∃I(IQL)(All)", []string{"Aaa"}, "∃uAuu", pr.Positive, pr.NoModality, 1},
	{"∃E(1QL)(0-ary)", []string{"∃uA"}, "A", pr.Positive, pr.NoModality, 1},
	{"∃E(1QL)(n-ary)", []string{"∃u((u=u)→Aab)"}, "Aab", pr.Positive, pr.NoModality, 1},
	{"∃E(1QL)(Swap)", []string{"∃u∃vAuv"}, "∃v∃uAvu", pr.Positive, pr.NoModality, 1},
	{"∃E(1QL)(Move)", []string{"∃u∃vAuv"}, "∃v∃uAuv", pr.Positive, pr.NoModality, 1},
	{"∃I(2QL)(0-ary)", nil, "∃U⊤", pr.Positive, pr.NoModality, 1},
	{"∃I(2QL)(1L)", []string{"Aa→Aa"}, "∃U(Ua→Aa)", pr.Positive, pr.NoModality, 1},
	{"∃I(2QL)(1R)", []string{"Aa→Aa"}, "∃U(Aa→Ua)", pr.Positive, pr.NoModality, 1},
	{"∃I(2QL)(All)", []string{"Aa→Aa"}, "∃U(Ua→Ua)", pr.Positive, pr.NoModality, 1},
	{"∃E(2QL)(0-ary)", []string{"∃UA"}, "A", pr.Positive, pr.NoModality, 1},
	{"∃E(2QL)(n-ary)", []string{"∃U((U→U)→A)"}, "A", pr.Positive, pr.NoModality, 1},
	{"∃E(1QL)(Swap)", []string{"∃U∃V(Ua∨Va)"}, "∃V∃U(Va∨Ua)", pr.Positive, pr.NoModality, 1},
	{"∃E(1QL)(Move)", []string{"∃U∃V(Ua∨Va)"}, "∃V∃U(Ua∨Va)", pr.Positive, pr.NoModality, 1},
	{"□Con", nil, "□(A∨B)→□(B∨A)", pr.Positive, pr.ModalEw, 1},
	{"◇Con", nil, "◇(A∨B)→◇(B∨A)", pr.Positive, pr.ModalEw, 1},
	{"□Ew", []string{"□⊤", "□⊥"}, "¬◇⊥∧¬◇⊤", pr.Minimal, pr.ModalEw, 1},
	{"◇Ew", []string{"◇⊤", "◇⊥"}, "¬□⊥∧¬□⊤", pr.Minimal, pr.ModalEw, 1},
	{"◇I", []string{"¬□¬A"}, "◇A", pr.Classical, pr.ModalEw, 1},
	{"□En", []string{"□A", "□¬B"}, "¬◇¬A∧¬◇B", pr.Minimal, pr.ModalEn, 1},
	{"◇En", []string{"◇A", "◇¬B"}, "¬□¬A∧¬□B", pr.Minimal, pr.ModalEn, 1},
	{"□Es", []string{"□A"}, "¬◇(B∧¬B)", pr.Minimal, pr.ModalEs, 1},
	{"◇Es", []string{"◇A"}, "¬□(B∧¬B)", pr.Minimal, pr.ModalEs, 1},
	{"□Mon", nil, "□A→□(A∨B)", pr.Positive, pr.ModalM, 1},
	{"◇Mon", nil, "◇A→◇(A∨B)", pr.Positive, pr.ModalM, 1},
	{"□E", []string{"□(A∧B)"}, "□A∧□B", pr.Positive, pr.ModalM, 1},
	{"◇E", []string{"◇A"}, "◇(A∨B)", pr.Positive, pr.ModalM, 1},
	{"□I", nil, "□(A→(A∨B))", pr.Positive, pr.ModalN, 1},
	{"¬◇I", nil, "¬◇⊥", pr.Minimal, pr.ModalN, 1},
	{"□Agg", []string{"□A", "□B"}, "□(A∧B)", pr.Positive, pr.ModalC, 1},
	{"Reit[C]", []string{"□A", "□(A→B)"}, "□B", pr.Positive, pr.ModalM * pr.ModalC, 1},
	{"Reit[K]", []string{"◇A", "□(A→B)"}, "◇B", pr.Positive, pr.ModalK, 1},
	{"D", []string{"□A"}, "◇A", pr.Positive, pr.ModalD, 1},
	{"TI", []string{"A"}, "◇A", pr.Positive, pr.ModalT, 1},
	{"TE", []string{"□A"}, "A", pr.Positive, pr.ModalT, 1},
	{"4I", []string{"□A"}, "□□A", pr.Positive, pr.Modal4, 1},
	{"4E", []string{"◇◇A"}, "◇A", pr.Positive, pr.Modal4, 1},
	{"BI", []string{"A"}, "□◇A", pr.Positive, pr.ModalB, 1},
	{"BE", []string{"◇□A"}, "A", pr.Positive, pr.ModalB, 1},
	{"5I", []string{"◇A"}, "□◇A", pr.Positive, pr.Modal5, 1},
	{"5E", []string{"◇□A"}, "□A", pr.Positive, pr.Modal5, 1},
	// Major Axiomatizations
	{"Weakening", nil, "A→(B→A)", pr.Implicational, pr.NoModality, 1},
	{"Frege 2", nil, "(A→(B→C))→((A→B)→(A→C))", pr.Implicational, pr.NoModality, 1},
	{"Contraction", nil, "(A→(A→B))→(A→B)", pr.Implicational, pr.NoModality, 1},
	{"Meredith 1", nil, "A→((B→C)→(((D→B)→(C→E))→(B→E)))", pr.Implicational, pr.NoModality, 1},
	{"Meredith 2", nil, "(A→B)→((A→(B→C))→(A→C))", pr.Implicational, pr.NoModality, 1},
	{"Meredith 3", nil, "((A→B)→C)→(D→((B→(C→E))→(B→E)))", pr.Implicational, pr.NoModality, 1},
	{"Hyp Syll LR", nil, "(A→B)→((B→C)→(A→C))", pr.Implicational, pr.NoModality, 1},
	{"Hyp Syll RL", nil, "(A→B)→((C→A)→(C→B))", pr.Implicational, pr.NoModality, 1},
	{"Permutation", nil, "(A→(B→C))→(B→(A→C))", pr.Implicational, pr.NoModality, 1},
	{"Identity", nil, "A→A", pr.Implicational, pr.NoModality, 1},
	{"3-Prem ∨E", nil, "(A→B)→((C→B)→((A∨C)→B)) ", pr.Positive, pr.NoModality, 1},
	{"LNC ∧", nil, "¬(A∧¬A)", pr.Minimal, pr.NoModality, 1},
	{"LNC ↔", nil, "¬(A↔¬A)", pr.Minimal, pr.NoModality, 1},
	{"Contra (Min)", nil, "(A→¬B)→(B→¬A)", pr.Minimal, pr.NoModality, 1},
	{"Modus Tollens", nil, "(A→B)→(¬B→¬A)", pr.Minimal, pr.NoModality, 1},
	{"DNI", nil, "A→¬¬A", pr.Minimal, pr.NoModality, 1},
	{"DNE (Min)", nil, "¬¬¬A→¬A", pr.Minimal, pr.NoModality, 1},
	{"RAA 1", nil, "(A→¬A)→¬A", pr.Minimal, pr.NoModality, 1},
	{"RAA 2", nil, "(¬A→A)→¬¬A", pr.Minimal, pr.NoModality, 1},
	{"Explosion", nil, "¬A→(A→B)", pr.Intuitionistic, pr.NoModality, 1},
	{"WLEM ∨", nil, "¬A∨¬¬A", pr.Jankov, pr.NoModality, 1},
	{"¬∧ (Jan)", nil, "¬(A∧B)→(¬A∨¬B)", pr.Jankov, pr.NoModality, 1},
	{"¬¬∨ (Jan)", nil, "¬¬(A∨B)→(¬¬A∨¬¬B)", pr.Jankov, pr.NoModality, 1},
	{"WLIN", nil, "(A→¬A)∨(¬A→A)", pr.Jankov, pr.NoModality, 1},
	{"WDGP", nil, "(A→B)∨(¬A→¬B)", pr.Jankov, pr.NoModality, 1},
	{"NIP", nil, "(A→(B∨¬C))→((A→B)∨(A→¬C))", pr.Jankov, pr.NoModality, 1},
	{"Jan Elim", nil, "(¬A→B)→((¬¬A→B)→B)", pr.Jankov, pr.NoModality, 1},
	{"Jan Permutes", nil, "(¬A→(B→C))→((B→(¬¬A→C))→(B→C))", pr.Jankov, pr.NoModality, 1},
	{"Limited LEM", nil, "(¬¬A→A)→(A∨¬A)", pr.Jankov, pr.NoModality, 1},
	{"WLEM →", nil, "(A→B)→(¬A∨¬¬B)", pr.Jankov, pr.NoModality, 1},
	{"WLEM ¬", nil, "¬¬A∨¬¬¬A", pr.Jankov, pr.NoModality, 1},
	{"DGP", nil, "(A→B)∨(B→A)", pr.GödelDummett, pr.NoModality, 1},
	{"Hosoi 1", nil, "(¬A∨B)∨(B→A)", pr.Smetanich, pr.NoModality, 1},
	{"Hosoi 2", nil, "¬A∨(B∨(B→A))", pr.Smetanich, pr.NoModality, 1},
	{"Hosoi 3", nil, "A∨(¬B∨(A→B))", pr.Smetanich, pr.NoModality, 1},
	{"DNE (Cls)", nil, "¬¬A→A", pr.Classical, pr.NoModality, 1},
	{"Contra (Cls)", nil, "(¬A→¬B)→(B→A)", pr.Classical, pr.NoModality, 1},
	{"LEM", nil, "A∨¬A", pr.Classical, pr.NoModality, 1},
	{"Peirce", nil, "((A→B)→A)→A", pr.Classical, pr.NoModality, 1},
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

		pass = t.Run(tc.title+" Test", func(t *testing.T) {
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
