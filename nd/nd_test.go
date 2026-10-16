package nd_test

import (
	"Deriver/fmla"
	"Deriver/nd"
	"Deriver/nd/pr"
	"testing"
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
	inf   pr.InfStrength
	mod   pr.ModStrength
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
	{"∨E(L)", []string{"A∨B", "A→C"}, "C∨B", pr.Positive, pr.NoModality, 1},
	{"∨E(R)", []string{"A∨B", "B→C"}, "A∨C", pr.Positive, pr.NoModality, 1},
	{"∨E(B)", []string{"A∨A", "A→B"}, "B", pr.Positive, pr.NoModality, 1},
	{"↔I", []string{"A→B", "B→A"}, "A↔B", pr.Positive, pr.NoModality, 1},
	{"↔E(L)", []string{"A↔B", "A"}, "B", pr.Positive, pr.NoModality, 1},
	{"↔E(R)", []string{"A↔B", "B"}, "A", pr.Positive, pr.NoModality, 1},
	{"⊥I", []string{"A", "¬A"}, "⊥", pr.Minimal, pr.NoModality, 1},
	{"¬I", []string{"A→⊥"}, "¬A", pr.Intuitionistic, pr.NoModality, 1},
	{"⊥E", []string{"⊥"}, "A", pr.Intuitionistic, pr.NoModality, 1},
	{"Jan(L)", []string{"A→¬B"}, "¬A∨¬B", pr.Jankov, pr.NoModality, 1},
	{"Jan(R)", []string{"A→¬B"}, "¬B∨¬A", pr.Jankov, pr.NoModality, 1},
	{"Göd(L)", []string{"(A→B)→C"}, "C∨(B→A)", pr.GödelDummett, pr.NoModality, 1},
	{"Göd(R)", []string{"(A→B)→C"}, "(B→A)∨C", pr.GödelDummett, pr.NoModality, 1},
	{"Sme(L)", []string{"(A→B)→A"}, "A∨¬B", pr.Smetanich, pr.NoModality, 1},
	{"Sme(R)", []string{"(A→B)→A"}, "¬B∨A", pr.Smetanich, pr.NoModality, 1},
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

	{"Dal/K□", nil, "□(A→B)→(□A→□B)", pr.Positive, pr.ModalM * pr.ModalC, 1},
}

func TestDeriveAtStrength(t *testing.T) {
	var (
		tc   testCase
		drv  *nd.Drv
		pass bool
	)

	for _, tc = range testCases {
		drv = nd.NewDeriver(tc.inf, tc.mod, ndTestParseWff(t, tc.goal), ndTestParseWffs(t, tc.prems...)...)

		pass = t.Run(tc.title+" Test", func(t *testing.T) {
			var (
				fitch string
			)

			if !drv.DeriveAtStrength() {
				t.Errorf("Derivation failed.")
			} else {
				// _ = drv.Prf.Prune()
			}

			fitch = drv.Prf.FitchFormat()

			t.Logf("\n%s\n", fitch)

			_ = drv.Prf.Prune()

			fitch = drv.Prf.FitchFormat()

			t.Logf("\n%s\n", fitch)
		})

		if !pass {
			break
		}
	}
}
