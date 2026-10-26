package pr_test

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
	"fmt"
	"testing"
)

type synTestCase struct {
	name      string
	wffs      []*fmla.Wff
	want      pr.SynBreadth
	ruleTests map[pr.NDRule]bool // Indicate whether a rule fits this SynBreadth.
}

var synTestCases []synTestCase = []synTestCase{
	{
		"Empty Slice is Base Logic (1)",
		[]*fmla.Wff{},
		1,
		map[pr.NDRule]bool{pr.Solve: true, pr.Prem: true, pr.Ass: true, pr.WedgeE: false},
	},
	{
		"Multiple PL WFFs Yield PL",
		[]*fmla.Wff{fmla.MustParseWff("A→¬B"), fmla.MustParseWff("C∧A"), fmla.MustParseWff("¬B↔⊥")},
		pr.PL,
		map[pr.NDRule]bool{pr.VeeI: true, pr.NegE: true, pr.Jan: true, pr.ExistsI: false},
	},
	{
		"PL WFFs with One Identity Predicate Yield PL*NL*I",
		[]*fmla.Wff{fmla.MustParseWff("A"), fmla.MustParseWff("B"), fmla.MustParseWff("a=b")},
		pr.PL * pr.NL * pr.I,
		map[pr.NDRule]bool{pr.EqualE: true, pr.ForAllE: false},
	},
	{
		"PL WFFs with One Quantifier Yield PL*NL*QL",
		[]*fmla.Wff{fmla.MustParseWff("A"), fmla.MustParseWff("A↔C"), fmla.MustParseWff("∀uAu")},
		pr.PL * pr.NL * pr.QL,
		map[pr.NDRule]bool{pr.ForAllE: true, pr.ExistsE: true, pr.BoxE: false, pr.Intro4: false},
	},
	{
		"PL WFFs with One Modal Operator Yield PL*ML",
		[]*fmla.Wff{fmla.MustParseWff("¬¬A∨¬B"), fmla.MustParseWff("□(A→B)")},
		pr.PL * pr.ML,
		map[pr.NDRule]bool{pr.BoxE: true, pr.DmdE: true, pr.ForAllE: false, pr.EqualI: false},
	},
	{
		"NL WFFs with One Modal Operator Yield PL*NL*ML",
		[]*fmla.Wff{fmla.MustParseWff("Aa→Bab"), fmla.MustParseWff("□A")},
		pr.PL * pr.NL * pr.ML,
		map[pr.NDRule]bool{pr.RuleD: true, pr.ReitK: true, pr.EqualI: false, pr.ExistsE: false},
	},
}

func TestSynBreadthOfWffs(t *testing.T) {
	var (
		stc synTestCase
	)

	for _, stc = range synTestCases {
		t.Run(stc.name, func(t *testing.T) {
			var (
				syn pr.SynBreadth
			)

			if syn = pr.SynBreadthOfWffs(stc.wffs...); syn != stc.want {
				t.Fatalf("SynBreadthOfWffs() = %v, want %v.", syn, stc.want)
			}
		})
	}
}

func TestRuleFitsSynBreadth(t *testing.T) {
	var (
		stc  synTestCase
		rule pr.NDRule
		exp  bool
	)

	for _, stc = range synTestCases {
		for rule, exp = range stc.ruleTests {
			if pr.RuleFitsSynBreadth(rule, stc.want) != exp {
				t.Fatalf("RuleFitsSynBreadth(%v, %v) = %v, want %v.", rule, stc.want, !exp, exp)
			}
		}
	}

	t.Run("Unrecognized Rule Panics", func(t *testing.T) {
		defer func() {
			var (
				rec any
				msg string
				ok  bool
			)

			if rec = recover(); rec == nil {
				t.Fatalf("Expected panic, but no panic occurred.")
			} else if msg, ok = rec.(string); !ok || msg != "Unrecognized rule." {
				t.Fatalf("Expected panic message %q, got %v.", "Unrecognized rule.", rec)
			}
		}()

		_ = pr.RuleFitsSynBreadth(pr.NDRule(255), pr.PL)
	})
}

func TestHasAnyModality(t *testing.T) {
	var (
		mods []pr.ModSt
		mod  pr.ModSt
	)

	mods = []pr.ModSt{pr.NoModality, pr.ModalEw, pr.ModalEn, pr.ModalEs, pr.ModalM, pr.ModalN, pr.ModalC,
		pr.ModalK, pr.ModalD, pr.ModalT, pr.Modal4, pr.ModalB, pr.Modal5}

	t.Run("Each Modality Has No Modality as Strength", func(t *testing.T) {
		for _, mod = range mods {
			if !pr.HasAnyModality(mod, pr.NoModality) {
				t.Fatalf("Modality %d lacks non-modality as strength.", mod)
			}
		}
	})

	t.Run("All Modalities Have Any Modality as Strength", func(t *testing.T) {
		var prod pr.ModSt

		prod = pr.NoModality

		for _, mod = range mods {
			prod *= mod
		}

		for _, mod = range mods {
			if !pr.HasAnyModality(prod, mod) {
				t.Fatalf("The union of all modalities %d lacks modality %d as strength.", prod, mod)
			}
		}
	})
}

type ruleFitsTestCase struct {
	rule   pr.NDRule
	inf    pr.InfSt
	mod    pr.ModSt
	want   bool
	panics bool
	msg    string
}

var ruleFitsTestCases []ruleFitsTestCase = []ruleFitsTestCase{
	// Structural and Propositional Logic Boundaries
	{pr.Solve, pr.NoInference, pr.NoModality, true, false, ""},
	{pr.TopI, pr.NoInference, pr.NoModality, false, false, ""},
	{pr.TopI, pr.Implicational, pr.NoModality, true, false, ""},
	{pr.WedgeI, pr.Implicational, pr.NoModality, false, false, ""},
	{pr.WedgeI, pr.Positive, pr.NoModality, true, false, ""},
	{pr.BotI, pr.Positive, pr.NoModality, false, false, ""},
	{pr.BotI, pr.Minimal, pr.NoModality, true, false, ""},
	{pr.BotE, pr.Minimal, pr.NoModality, false, false, ""},
	{pr.BotE, pr.Intuitionistic, pr.NoModality, true, false, ""},

	// Intermediate Logics Thresholds
	{pr.Jan, pr.Intuitionistic, pr.NoModality, false, false, ""},
	{pr.Jan, pr.Jankov, pr.NoModality, true, false, ""},
	{pr.Göd, pr.Jankov, pr.NoModality, false, false, ""},
	{pr.Göd, pr.GödelDummett, pr.NoModality, true, false, ""},
	{pr.Sme, pr.GödelDummett, pr.NoModality, false, false, ""},
	{pr.Sme, pr.Smetanich, pr.NoModality, true, false, ""},
	{pr.NegE, pr.Smetanich, pr.NoModality, false, false, ""},
	{pr.NegE, pr.Classical, pr.NoModality, true, false, ""},

	// Quantificational and Identity Limits
	{pr.EqualI, pr.NoInference, pr.NoModality, false, false, ""},
	{pr.EqualI, pr.Implicational, pr.NoModality, true, false, ""},
	{pr.ForAllI, pr.Implicational, pr.NoModality, false, false, ""},
	{pr.ForAllI, pr.Positive, pr.NoModality, true, false, ""},

	// Standard Non-Normal and Normal Modalities
	{pr.BoxCon, pr.Positive, pr.ModalEw, true, false, ""},
	{pr.BoxCon, pr.Positive, pr.NoModality, false, false, ""},
	{pr.BoxCon, pr.Implicational, pr.ModalEw, false, false, ""},
	{pr.DmdI, pr.Smetanich, pr.ModalEw, false, false, ""},
	{pr.DmdI, pr.Classical, pr.ModalEw, true, false, ""},
	{pr.BoxIntEw, pr.Minimal, pr.ModalEn, true, false, ""},
	{pr.BoxIntEn, pr.Minimal, pr.ModalEn, true, false, ""},
	{pr.BoxIntEs, pr.Minimal, pr.ModalEn, false, false, ""},

	// DmdIntEn Special Negative Constraint in MPL+EnC
	{pr.DmdIntEn, pr.Minimal, pr.ModalEn, true, false, ""},
	{pr.DmdIntEn, pr.Minimal, pr.ModalEn * pr.ModalC, false, false, ""},
	{pr.DmdIntEn, pr.Minimal, pr.ModalEs * pr.ModalC, true, false, ""},

	// Modal Extensions and Strict Sub-modality Limits
	{pr.DmdMon, pr.Implicational, pr.ModalM, false, false, ""},
	{pr.DmdMon, pr.Positive, pr.ModalM, true, false, ""},
	{pr.DmdE, pr.Implicational, pr.ModalM, false, false, ""},
	{pr.DmdE, pr.Positive, pr.ModalM, true, false, ""},
	{pr.BoxI, pr.Implicational, pr.ModalN, false, false, ""},
	{pr.BoxI, pr.Positive, pr.ModalN, true, false, ""},
	{pr.NegDmdI, pr.Positive, pr.ModalN, false, false, ""},
	{pr.NegDmdI, pr.Minimal, pr.ModalN, true, false, ""},
	{pr.ReitC, pr.Implicational, pr.ModalC, false, false, ""},
	{pr.ReitC, pr.Positive, pr.ModalC, true, false, ""},
	{pr.ReitK, pr.Positive, pr.ModalM, false, false, ""},
	{pr.ReitK, pr.Positive, pr.ModalK, true, false, ""},
	{pr.RuleD, pr.Positive, pr.ModalD, true, false, ""},
	{pr.IntroT, pr.Positive, pr.ModalT, true, false, ""},
	{pr.Elim4, pr.Positive, pr.Modal4, true, false, ""},
	{pr.IntroB, pr.Positive, pr.ModalB, true, false, ""},
	{pr.Intro5, pr.Positive, pr.Modal5, true, false, ""},

	// Unrecognized Rule Panic Guardrail
	{pr.NDRule(255), pr.NoInference, pr.NoModality, false, true, "Unrecognized rule."},
}

func TestRuleFitsStrengths(t *testing.T) {
	var (
		rtc  ruleFitsTestCase
		name string
	)

	for _, rtc = range ruleFitsTestCases {
		name = fmt.Sprintf("Rule=%v,Inf=%v,Mod=%v", rtc.rule, rtc.inf, rtc.mod)

		t.Run(name, func(t *testing.T) {
			var is bool

			if rtc.panics {
				defer func() {
					var (
						rec any
						msg string
						ok  bool
					)

					if rec = recover(); rec == nil {
						t.Fatalf("Expected panic with message %q, but no panic occurred.", rtc.msg)
					} else if msg, ok = rec.(string); !ok || msg != rtc.msg {
						t.Fatalf("Expected panic message %q, got %v.", rtc.msg, rec)
					}
				}()

				_ = pr.RuleFitsStrengths(rtc.rule, rtc.inf, rtc.mod)
			} else {
				is = pr.RuleFitsStrengths(rtc.rule, rtc.inf, rtc.mod)

				if is != rtc.want {
					t.Fatalf("RuleFitsStrengths(%v, %v, %v) = %v, want %v.", rtc.rule, rtc.inf, rtc.mod, is, rtc.want)
				}
			}
		})
	}
}

type nameTestCase struct {
	inf  pr.InfSt
	syn  pr.SynBreadth
	mod  pr.ModSt
	want string
}

var nameTestCases []nameTestCase = []nameTestCase{
	{pr.Implicational, pr.QL, pr.NoModality, "TQL"},
	{pr.Positive, pr.NL, pr.NoModality, "PNL"},
	{pr.Positive, pr.NL * pr.I, pr.NoModality, "PNLi"},
	{pr.Minimal, pr.PL, pr.NoModality, "MPL"},
	{pr.Intuitionistic, pr.PL * pr.QL, pr.NoModality, "IQL"},
	{pr.Jankov, pr.PL * pr.NL, pr.NoModality, "JNL"},
	{pr.GödelDummett, pr.PL * pr.NL * pr.QL, pr.NoModality, "GQL"},
	{pr.Smetanich, pr.PL * pr.NL * pr.I, pr.NoModality, "SNLi"},
	{pr.Classical, pr.PL * pr.NL * pr.QL * pr.I, pr.NoModality, "CQLi"},
	{pr.Positive, pr.NL * pr.ML * pr.I, pr.ModalM, "PNLi+M"},
	{pr.Positive, pr.PL * pr.ML, pr.ModalC * pr.ModalM, "PPL+MC"},
	{pr.Classical, pr.QL * pr.NL * pr.I * pr.ML, pr.ModalEs * pr.ModalN, "CQLi+EsN"},
	{pr.Jankov, pr.PL * pr.ML, pr.ModalEw * pr.Modal4 * pr.ModalD, "JPL+EwD4"},
	{pr.GödelDummett, pr.PL * pr.ML, pr.ModalM * pr.ModalK * pr.ModalT * pr.Modal5, "GPL+KT5"},
}

func TestNameLogic(t *testing.T) {
	var (
		ntc  nameTestCase
		name string
	)

	for _, ntc = range nameTestCases {
		if name = pr.NameLogic(ntc.inf, ntc.syn, ntc.mod); name != ntc.want {
			t.Fatalf("NameLogic(%v, %v, %v) = %q, want %q.", ntc.inf, ntc.syn, ntc.mod, name, ntc.want)
		}
	}
}

type extractTestCase struct {
	name   string
	inf    pr.InfSt
	syn    pr.SynBreadth
	mod    pr.ModSt
	panics bool
	msg    string
}

var extractTestCases []extractTestCase = []extractTestCase{
	{"", 0, 0, 0, true, "Incomplete logic name."},
	{"T", 0, 0, 0, true, "Missing syntactic breadth."},
	{"TPL", pr.Implicational, pr.PL, pr.NoModality, false, ""},
	{"PNL", pr.Positive, pr.PL * pr.NL, pr.NoModality, false, ""},
	{"MQL", pr.Minimal, pr.PL * pr.NL * pr.QL, pr.NoModality, false, ""},
	{"INLi", pr.Intuitionistic, pr.PL * pr.NL * pr.I, pr.NoModality, false, ""},
	{"JPL+Ew", pr.Jankov, pr.PL * pr.ML, pr.ModalEw, false, ""},
	{"GNL+En", pr.GödelDummett, pr.PL * pr.NL * pr.ML, pr.ModalEn, false, ""},
	{"SQLi+Es", pr.Smetanich, pr.PL * pr.NL * pr.QL * pr.I * pr.ML, pr.ModalEs, false, ""},
	{"CPL+MD", pr.Classical, pr.PL * pr.ML, pr.ModalM * pr.ModalD, false, ""},
	{"XNL", 0, 0, 0, true, "Unrecognized inferential strength."},
	{"PAL", 0, 0, 0, true, "Unrecognized syntactic breadth."},
	{"TQL+E", 0, 0, 0, true, "Unrecognized modality."},
	{"TQL+Ep", 0, 0, 0, true, "Unrecognized modality."},
	{"CPL+MCNT", pr.Classical, pr.PL * pr.ML, pr.ModalM * pr.ModalC * pr.ModalN * pr.ModalT, false, ""},
	{"SNLi+B5", pr.Smetanich, pr.PL * pr.NL * pr.I * pr.ML, pr.ModalB * pr.Modal5, false, ""},
	{"JPL+X", 0, 0, 0, true, "Unrecognized modality."},
	{"GNL-K", 0, 0, 0, true, "Unrecognized logic."},
}

func TestExtractLogic(t *testing.T) {
	var (
		etc extractTestCase
	)

	for _, etc = range extractTestCases {
		t.Run("Extraction of "+etc.name, func(t *testing.T) {
			var (
				inf pr.InfSt
				syn pr.SynBreadth
				mod pr.ModSt
			)

			if etc.panics {
				defer func() {
					var (
						rec any
						msg string
						ok  bool
					)

					if rec = recover(); rec == nil {
						t.Fatalf("Expected panic with message %q, but no panic occurred.", etc.msg)
					} else if msg, ok = rec.(string); !ok || msg != etc.msg {
						t.Fatalf("Expected panic message %q, got %v", etc.msg, rec)
					}
				}()

				_, _, _ = pr.ExtractLogic(etc.name)
			} else {
				inf, syn, mod = pr.ExtractLogic(etc.name)

				switch {
				case inf != etc.inf:
					t.Fatalf("ExtractLogic(%q)'s inferential strength = %v, wants %v.", etc.name, inf, etc.inf)
				case syn != etc.syn:
					t.Fatalf("ExtractLogic(%q)'s syntactic breadth = %v, want %v.", etc.name, syn, etc.syn)
				case mod != etc.mod:
					t.Fatalf("ExtractLogic(%q)'s modal strength = %v, want %v.", etc.name, mod, etc.mod)
				}
			}
		})
	}
}
