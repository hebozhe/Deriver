package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
	"testing"
)

func ndTestParseWff(t *testing.T, s string) (wff *fmla.Wff) {
	var ok bool

	t.Helper()

	if wff, ok = fmla.ParseStringToWff(s); !ok {
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
		if wff, ok = fmla.ParseStringToWff(s); !ok {
			t.Fatalf("Failed to parse %q.", s)
		}

		wffs = append(wffs, wff)
	}

	return
}

type testCase struct {
	prems []string
	goal  string
	infS  pr.InfStrength
	modS  pr.ModStrength
}

var tcs []testCase = []testCase{
	// == Immediate Derivations ==
	// Implicational Propositional Logic (TPL)...
	{nil, "⊤", pr.Implicational, pr.NoModality},                  // TopIntro
	{nil, "A→⊤", pr.Implicational, pr.NoModality},                // ToIntro
	{[]string{"A→B", "A"}, "B", pr.Implicational, pr.NoModality}, // ToElim
	{[]string{"A", "A→B"}, "B", pr.Implicational, pr.NoModality}, // ToElim
	{[]string{"B"}, "A→B", pr.Implicational, pr.NoModality},      // ToIntro
	{[]string{"A"}, "B→(C→A)", pr.Implicational, pr.NoModality},  // Reiteration
	// Positive Propositional Logic (PPL)...
	{[]string{"A", "B"}, "A∧B", pr.Positive, pr.NoModality},          // WedgeIntro
	{[]string{"B", "A"}, "A∧B", pr.Positive, pr.NoModality},          // WedgeIntro
	{[]string{"A∧B"}, "A", pr.Positive, pr.NoModality},               // WedgeElim
	{[]string{"A∧B"}, "B", pr.Positive, pr.NoModality},               // WedgeElim
	{[]string{"A"}, "A∨B", pr.Positive, pr.NoModality},               // VeeIntro
	{[]string{"B"}, "A∨B", pr.Positive, pr.NoModality},               // VeeIntro
	{[]string{"A∨B", "A→C", "B→C"}, "C", pr.Positive, pr.NoModality}, // VeeElim
	{[]string{"A→C", "A∨B", "B→C"}, "C", pr.Positive, pr.NoModality}, // VeeElim
	{[]string{"A→C", "B→C", "A∨B"}, "C", pr.Positive, pr.NoModality}, // VeeElim
	{[]string{"B→C", "A→C", "A∨B"}, "C", pr.Positive, pr.NoModality}, // VeeElim
	{[]string{"B→C", "A∨B", "A→C"}, "C", pr.Positive, pr.NoModality}, // VeeElim
	{[]string{"A∨B", "B→C", "A→C"}, "C", pr.Positive, pr.NoModality}, // VeeElim
	{[]string{"A→B", "B→A"}, "A↔B", pr.Positive, pr.NoModality},      // IffIntro
	{[]string{"B→A", "A→B"}, "A↔B", pr.Positive, pr.NoModality},      // IffIntro
	{[]string{"A↔B"}, "A→B", pr.Positive, pr.NoModality},             // IffElim
	{[]string{"A↔B"}, "B→A", pr.Positive, pr.NoModality},             // IffElim
	// Minimal Propositional Logic (MPL)...
	{[]string{"A", "¬A"}, "⊥", pr.Minimal, pr.NoModality}, // BotIntro
	{[]string{"¬A", "A"}, "⊥", pr.Minimal, pr.NoModality}, // BotIntro
	{[]string{"A"}, "¬¬A", pr.Minimal, pr.NoModality},     // NegIntro
	// Intuitionistic Propositional Logic (IPL)...
	{[]string{"⊥"}, "A", pr.Intuitionistic, pr.NoModality}, // BotElim
	// Classical Propositional Logic (CPL)...
	{[]string{"¬¬A"}, "A", pr.Classical, pr.NoModality}, // NegElim
	// Positive 1st- and 2nd-Order Quantificational Logic (P[12]QL)...
	{nil, "∀u⊤", pr.Positive, pr.NoModality},                           // ForAllIntro
	{nil, "∀U⊤", pr.Positive, pr.NoModality},                           // ForAllIntro
	{[]string{"∀uA"}, "A", pr.Positive, pr.NoModality},                 // ForAllElim
	{[]string{"∀uAa"}, "Aa", pr.Positive, pr.NoModality},               // ForAllElim
	{[]string{"∀UAa"}, "Aa", pr.Positive, pr.NoModality},               // ForAllElim
	{[]string{"∀uAu"}, "Aa", pr.Positive, pr.NoModality},               // ForAllElim
	{[]string{"∀UUa"}, "Aa", pr.Positive, pr.NoModality},               // ForAllElim
	{[]string{"∀u∀vAuv"}, "∀v∀uAuv", pr.Positive, pr.NoModality},       // ForAllElim, ForAllIntro
	{[]string{"∀u∀v∀wAuv"}, "∀v∀uAvu", pr.Positive, pr.NoModality},     // ForAllElim, ForAllIntro
	{[]string{"∀u∀v∀wAuvw"}, "∀w∀v∀uAuvw", pr.Positive, pr.NoModality}, // ForAllElim, ForAllIntro
	{[]string{"∀u∀v∀wAuvw"}, "∀w∀v∀uAwvu", pr.Positive, pr.NoModality}, // ForAllElim, ForAllIntro
	{nil, "∃u⊤", pr.Positive, pr.NoModality},                           // ExistsIntro
	{nil, "∃U⊤", pr.Positive, pr.NoModality},                           // ExistsIntro
	{[]string{"Aa"}, "∃uAu", pr.Positive, pr.NoModality},               // ExistsIntro
	{[]string{"Aa"}, "∃UUa", pr.Positive, pr.NoModality},               // ExistsIntro
	{[]string{"Aaa"}, "∃uAau", pr.Positive, pr.NoModality},             // ExistsIntro
	{[]string{"Aaa"}, "∃uAua", pr.Positive, pr.NoModality},             // ExistsIntro
	{[]string{"Aaa"}, "∃uAuu", pr.Positive, pr.NoModality},             // ExistsIntro
	{[]string{"∃uA"}, "A", pr.Positive, pr.NoModality},                 // ExistsElim
	{[]string{"∃UA"}, "A", pr.Positive, pr.NoModality},                 // ExistsElim
	{[]string{"∃u∃vAuv"}, "∃v∃uAuv", pr.Positive, pr.NoModality},       // ExistsElim, ExistsIntro
	{[]string{"∃u∃vAuv"}, "∃v∃uAvu", pr.Positive, pr.NoModality},       // ExistsElim, ExistsIntro
	{[]string{"∃u∃v∃wAuvw"}, "∃w∃v∃uAuvw", pr.Positive, pr.NoModality}, // ExistsElim, ExistsIntro
	{[]string{"∃u∃v∃wAuvw"}, "∃w∃v∃uAwvu", pr.Positive, pr.NoModality}, // ExistsElim, ExistsIntro
	// Implicational 1st-Order Predicate Logic with Identity (PNLi)...
	{nil, "a=a", pr.Implicational, pr.NoModality},                    // EqualsIntro
	{[]string{"a=b", "Aa"}, "Ab", pr.Implicational, pr.NoModality},   // EqualsElim
	{[]string{"a=b", "Aaa"}, "Aab", pr.Implicational, pr.NoModality}, // EqualsElim
	{[]string{"a=b", "Aaa"}, "Aba", pr.Implicational, pr.NoModality}, // EqualsElim
	{[]string{"a=b", "Aaa"}, "Abb", pr.Implicational, pr.NoModality}, // EqualsElim
	{[]string{"a=b"}, "b=a", pr.Implicational, pr.NoModality},        // EqualsIntro, EqualsElim
	{[]string{"a=b", "b=c"}, "a=c", pr.Implicational, pr.NoModality}, // EqualsIntro, EqualsElim
	{[]string{"a=b", "b=c"}, "c=a", pr.Implicational, pr.NoModality}, // EqualsIntro, EqualsElim
	// Positive Propositional Modal Logic K (PPL+K)...
	{nil, "□⊤", pr.Positive, pr.ModalK},
	{[]string{"□A", "□(A→B)"}, "□B", pr.Positive, pr.ModalK},
	{[]string{"◇A", "□(A→B)"}, "◇B", pr.Positive, pr.ModalK},
	// Minimal Propositional Modal Logic K (MPL+K)...
	{[]string{"¬◇A"}, "□¬A", pr.Minimal, pr.ModalK},
	{[]string{"◇⊥"}, "⊥", pr.Minimal, pr.ModalK},
	// Classical Propositional Modal Logic K (CPL+K)...
	{[]string{"¬□A"}, "◇¬A", pr.Classical, pr.ModalK},
	{[]string{"¬□¬A"}, "◇¬¬A", pr.Classical, pr.ModalK},
	{[]string{"¬□¬A"}, "◇A", pr.Classical, pr.ModalK},
	// Positive Propositional Modal Logic D (PPL+D)...
	{[]string{"□A"}, "◇A", pr.Positive, pr.ModalD},
	// Positive Propositional Modal Logic M (PPL+M)...
	{[]string{"□A"}, "A", pr.Positive, pr.ModalM},
	{[]string{"A"}, "◇A", pr.Positive, pr.ModalM},
	// Positive Propositional Modal Logic 4 (PPL+4)...
	{[]string{"□A"}, "□□A", pr.Positive, pr.Modal4},
	{[]string{"◇◇A"}, "◇A", pr.Positive, pr.Modal4},
	// Positive Propositional Modal Logic B (PPL+B)...
	{[]string{"A"}, "□◇A", pr.Positive, pr.ModalB},
	{[]string{"◇□A"}, "A", pr.Positive, pr.ModalB},

	// == Propositional Theorems ==
	// TPL...
	{nil, "A→A", pr.Implicational, pr.NoModality},                             // →-Identity
	{nil, "A→(B→A)", pr.Implicational, pr.NoModality},                         // Weakening
	{nil, "A→((A→B)→B)", pr.Implicational, pr.NoModality},                     // Assertion Theorem
	{nil, "A→(B→(C→(D→A)))", pr.Implicational, pr.NoModality},                 // Deep Reiteration
	{nil, "(A→(A→B))→(A→B)", pr.Implicational, pr.NoModality},                 // Contraction
	{nil, "((A→B)→C)→(B→C)", pr.Implicational, pr.NoModality},                 // Implicational Exportation
	{nil, "(A→B)→(((A→B)→B)→B)", pr.Implicational, pr.NoModality},             // Triple Implication Collapse OI
	{nil, "(((A→B)→B)→B)→(A→B)", pr.Implicational, pr.NoModality},             // Triple Implication Collapse IO
	{nil, "(A→B)→((B→C)→(A→C))", pr.Implicational, pr.NoModality},             // Suffixing
	{nil, "(B→C)→((A→B)→(A→C))", pr.Implicational, pr.NoModality},             // Prefixing
	{nil, "(A→(B→C))→(B→(A→C))", pr.Implicational, pr.NoModality},             // Permutation
	{nil, "(A→(B→C))→((A→B)→(A→C))", pr.Implicational, pr.NoModality},         // Frege's Theorem
	{nil, "(A→B)→((A→(B→C))→(A→C))", pr.Implicational, pr.NoModality},         // Frege's Theorem
	{nil, "((A→B)→(A→C))→(A→(B→C))", pr.Implicational, pr.NoModality},         // Frege's Theorem
	{nil, "A→((B→C)→(((D→B)→(C→E))→(B→E)))", pr.Implicational, pr.NoModality}, // Meredith's Axiom 1
	{nil, "((A→B)→C)→(D→((B→(C→E))→(B→E)))", pr.Implicational, pr.NoModality}, // Meredith's Axiom 3
	// PPL...
	{nil, "A↔A", pr.Positive, pr.NoModality},                         // ↔-Identity
	{nil, "(A∧B)→A", pr.Positive, pr.NoModality},                     // ∧-Elim
	{nil, "(A∧B)→B", pr.Positive, pr.NoModality},                     // ∧-Elim
	{nil, "(A∧A)→A", pr.Positive, pr.NoModality},                     // ∧-Indempotency LR
	{nil, "A→(A∧A)", pr.Positive, pr.NoModality},                     // ∧-Indempotency RL
	{nil, "A→(A∨B)", pr.Positive, pr.NoModality},                     // ∨-Intro
	{nil, "B→(A∨B)", pr.Positive, pr.NoModality},                     // ∨-Intro
	{nil, "(A∨A)→A", pr.Positive, pr.NoModality},                     // ∨-Indempotency LR
	{nil, "A→(A∨A)", pr.Positive, pr.NoModality},                     // ∨-Indempotency RL
	{nil, "A→(B→(A∧B))", pr.Positive, pr.NoModality},                 // ∧-Intro
	{nil, "B→(A→(A∧B))", pr.Positive, pr.NoModality},                 // ∧-Intro
	{nil, "(A↔B)→(B↔A)", pr.Positive, pr.NoModality},                 // ↔-Commutativity
	{nil, "(A∧B)→(B∧A)", pr.Positive, pr.NoModality},                 // ∧-Commutativity
	{nil, "(A∨B)→(B∨A)", pr.Positive, pr.NoModality},                 // ∨-Commutativity
	{nil, "∃u(∃vAv→Au)", pr.Positive, pr.NoModality},                 // The Drinker Paradox ∃→
	{nil, "¬(A∧B)→(A→¬B)", pr.Minimal, pr.NoModality},                // Distribution of ¬∧ OI
	{nil, "(A→¬B)→¬(A∧B)", pr.Minimal, pr.NoModality},                // Distribution of ¬∧ IO
	{nil, "(A∨B)→(¬A→¬¬B)", pr.Minimal, pr.NoModality},               // Weak Disjunctive Syllogism
	{nil, "¬(A∨B)→(¬A∧¬B)", pr.Minimal, pr.NoModality},               // Distribution of ¬∨ OI
	{nil, "(¬A∧¬B)→¬(A∨B)", pr.Minimal, pr.NoModality},               // Distribution of ¬∨ IO
	{nil, "(¬A∨¬B)→¬(A∧B)", pr.Minimal, pr.NoModality},               // Distribution of ¬∧ IO-∨
	{nil, "(A∧B)→((A→B)↔A)", pr.Positive, pr.NoModality},             // Heyting ∧-Equivalence LR
	{nil, "((A→B)↔A)→(A∧B)", pr.Positive, pr.NoModality},             // Heyting ∧-Equivalence RL
	{nil, "(A→B)→((A∨B)↔B)", pr.Positive, pr.NoModality},             // P-MFC of → LR
	{nil, "((A∨B)↔B)→(A→B)", pr.Positive, pr.NoModality},             // P-MFC of → RL
	{nil, "((A∨B)∧(A→B))→B", pr.Positive, pr.NoModality},             // ∨(→)-Absorption
	{nil, "(A∨(A∧B))→(A∨B)", pr.Positive, pr.NoModality},             // ∨(∧)-Absorption
	{nil, "((A∧B)→C)→(A→(B→C))", pr.Positive, pr.NoModality},         // Positive Exportation LR
	{nil, "(A→(B→C))→((A∧B)→C)", pr.Positive, pr.NoModality},         // Positive Exportation RL
	{nil, "(A→B)→((B→A)→(A↔B))", pr.Positive, pr.NoModality},         // ↔-Intro
	{nil, "(A↔B)→((A→B)∧(B→A))", pr.Positive, pr.NoModality},         // ↔-Elim
	{nil, "(A∨B)→((A→C)→(C∨B))", pr.Positive, pr.NoModality},         // ∨-Elim (2-Premise)
	{nil, "(A∨B)→((B→C)→(A∨C))", pr.Positive, pr.NoModality},         // ∨-Elim (2-Premise)
	{nil, "(A→C)→((A∨B)→(C∨B))", pr.Positive, pr.NoModality},         // ∨-Elim (2-Premise)
	{nil, "(B→C)→((A∨B)→(A∨C))", pr.Positive, pr.NoModality},         // ∨-Elim (2-Premise)
	{nil, "((A∨B)∨C)→(A∨(B∨C))", pr.Positive, pr.NoModality},         // ∨-Associativity LR
	{nil, "(A∨(B∨C))→((A∨B)∨C)", pr.Positive, pr.NoModality},         // ∨-Associativity RL
	{nil, "((A∧B)∧C)→(A∧(B∧C))", pr.Positive, pr.NoModality},         // ∧-Associativity LR
	{nil, "(A∧(B∧C))→((A∧B)∧C)", pr.Positive, pr.NoModality},         // ∧-Associativity RL
	{nil, "(A∧B)→(((A∨B)↔B)↔A)", pr.Positive, pr.NoModality},         // P-MFC of ∧ LR
	{nil, "(((A∨B)↔B)↔A)→(A∧B)", pr.Positive, pr.NoModality},         // P-MFC of ∧ RL
	{nil, "((A↔B)∧(B↔C))→(A↔C)", pr.Positive, pr.NoModality},         // ↔-Transitivity
	{nil, "((A∨B)→C)→((A→C)∧(B→C))", pr.Positive, pr.NoModality},     // Distribution of (∨)→ OI
	{nil, "((A→C)∧(B→C))→((A∨B)→C)", pr.Positive, pr.NoModality},     // Distribution of (∨)→ IO
	{nil, "(A→(B∧C))→((A→B)∧(A→C))", pr.Positive, pr.NoModality},     // Distribution of →(∧) OI
	{nil, "((A→B)∧(A→C))→(A→(B∧C))", pr.Positive, pr.NoModality},     // Distribution of →(∧) IO
	{nil, "(A→C)→((B→C)→((A∨B)→C))", pr.Positive, pr.NoModality},     // ∨-Elim (3-Premise)
	{nil, "((A→B)∨(A→C))→(A→(B∨C))", pr.Positive, pr.NoModality},     // Distribution of →(∨) RL
	{nil, "(A∧(B∨C))→((A∧B)∨(A∧C))", pr.Positive, pr.NoModality},     // Distribution of ∧(∨) LR
	{nil, "((A∧B)∨(A∧C))→(A∧(B∨C))", pr.Positive, pr.NoModality},     // Distribution of ∧(∨) RL
	{nil, "(A∨(B∧C))→((A∨B)∧(A∨C))", pr.Positive, pr.NoModality},     // Distribution of ∨(∧) LR
	{nil, "((A∨B)∧(A∨C))→(A∨(B∧C))", pr.Positive, pr.NoModality},     // Distribution of ∨(∧) RL
	{nil, "((A∨B)∧((A→C)∧(B→D)))→(C∨D)", pr.Positive, pr.NoModality}, // Constructive Dilemma
	// MPL...
	{nil, "⊥→¬A", pr.Minimal, pr.NoModality},                   // Weak Explosion
	{nil, "A→¬¬A", pr.Minimal, pr.NoModality},                  // ¬¬-Intro
	{nil, "¬(A∧¬A)", pr.Minimal, pr.NoModality},                // ∧-Form Noncontradiction
	{nil, "¬(A↔¬A)", pr.Minimal, pr.NoModality},                // ↔-Form Noncontradiction
	{nil, "¬A→¬¬¬A", pr.Minimal, pr.NoModality},                // ¬¬¬-Intro
	{nil, "¬¬¬A→¬A", pr.Minimal, pr.NoModality},                // ¬¬¬-Elim
	{nil, "¬A→(A→⊥)", pr.Minimal, pr.NoModality},               // Heyting ¬-Equivalence LR
	{nil, "(A→⊥)→¬A", pr.Minimal, pr.NoModality},               // Heyting ¬-Equivalence RL
	{nil, "¬¬(A∨¬A)", pr.Minimal, pr.NoModality},               // Negated Excluded Middle
	{nil, "¬A→(A→¬B)", pr.Minimal, pr.NoModality},              // Weak Strengthening
	{nil, "¬(A→B)→¬B", pr.Minimal, pr.NoModality},              // Distribution of ¬→ OI-¬ (no IO)
	{nil, "¬¬A→¬¬¬¬A", pr.Minimal, pr.NoModality},              // Brouwer's Theorem IO
	{nil, "¬¬¬¬A→¬¬A", pr.Minimal, pr.NoModality},              // Brouwer's Theorem OI
	{nil, "(A→¬A)→¬A", pr.Minimal, pr.NoModality},              // ¬-Contraction
	{nil, "(¬A→A)→¬¬A", pr.Minimal, pr.NoModality},             // Weak Consequentia Mirabilis
	{nil, "(A→¬B)→(B→¬A)", pr.Minimal, pr.NoModality},          // Contraposition
	{nil, "(A→B)→(¬B→¬A)", pr.Minimal, pr.NoModality},          // ¬-Contraposition LR
	{nil, "¬(A→B)→(A→¬B)", pr.Minimal, pr.NoModality},          // Distribution of ¬→ OI-→ (no IO)
	{nil, "(¬¬A∧¬B)→¬(A→B)", pr.Minimal, pr.NoModality},        // Distribution of ¬→ IO-∧
	{nil, "(A→B)→(¬¬A→¬¬B)", pr.Minimal, pr.NoModality},        // Double Contraposition LR
	{nil, "(¬A→¬B)→(¬¬B→¬¬A)", pr.Minimal, pr.NoModality},      // ¬¬-Contraposition LR
	{nil, "(¬¬B→¬¬A)→(¬A→¬B)", pr.Minimal, pr.NoModality},      // ¬¬-Contraposition RL
	{nil, "¬¬(A→B)→(¬¬A→¬¬B)", pr.Minimal, pr.NoModality},      // Distribution of ¬¬→ OI
	{nil, "(A→B)→(¬(B∧C)→¬(A∧C))", pr.Minimal, pr.NoModality},  // Monotonicity of Negated Conjunction
	{nil, "(A→(B∨C))→(¬B→(¬C→¬A))", pr.Minimal, pr.NoModality}, // Implied Disjunct Contraposition
	{nil, "¬(A↔B)→((A→¬B)∧(B→¬A))", pr.Minimal, pr.NoModality}, // Distribution of ¬↔ OI
	{nil, "(¬(A→B)∨¬(B→A))→¬(A↔B)", pr.Minimal, pr.NoModality}, // Distribution of ¬↔ IO-∨
	// IPL...
	{nil, "⊥→A", pr.Intuitionistic, pr.NoModality},                    // Explosion
	{nil, "¬A→(A→B)", pr.Intuitionistic, pr.NoModality},               // Strengthening
	{nil, "(¬A∨B)→(A→B)", pr.Intuitionistic, pr.NoModality},           // Material Implication RL
	{nil, "((A→B)→A)→¬¬A", pr.Intuitionistic, pr.NoModality},          // Weak Peirce's Law
	{nil, "¬¬(((A→B)→A)→A)", pr.Intuitionistic, pr.NoModality},        // Glivenko's Peirce's Law
	{nil, "¬(A→B)→(¬¬A∧¬B)", pr.Intuitionistic, pr.NoModality},        // Distribution of ¬→ OI-∧
	{nil, "¬(A↔B)→(¬A↔¬¬B)", pr.Intuitionistic, pr.NoModality},        // Distribution of ¬↔ OI (no IO)
	{nil, "(¬¬A→¬¬B)→¬¬(A→B)", pr.Intuitionistic, pr.NoModality},      // Distribution of ¬¬→ IO
	{nil, "(¬¬A∨¬A)→(¬¬A∨(¬¬A→A))", pr.Intuitionistic, pr.NoModality}, // Rieger-Nishimura Upper Lattice Bound
	// CPL...
	{nil, "¬¬A→A", pr.Classical, pr.NoModality},                           // ¬¬-Elim
	{nil, "¬A∨¬¬A", pr.Classical, pr.NoModality},                          // Weak Excluded Middle
	{nil, "A∨¬A", pr.Classical, pr.NoModality},                            // Excluded Middle
	{nil, "A∨(A→B)", pr.Classical, pr.NoModality},                         // Principle of Classical Implication
	{nil, "(¬A→A)→A", pr.Classical, pr.NoModality},                        // Consequentia Mirabilis
	{nil, "(A→B)∨(B→A)", pr.Classical, pr.NoModality},                     // Gödel-Dummett Theorem
	{nil, "(A→B)∨(B→C)", pr.Classical, pr.NoModality},                     // Import-Export Disjunction
	{nil, "((A→B)→A)→A", pr.Classical, pr.NoModality},                     // Peirce's Law
	{nil, "(A→B)→(¬A∨B)", pr.Classical, pr.NoModality},                    // Material Implication LR
	{nil, "(A↔B)∨(A↔¬B)", pr.Classical, pr.NoModality},                    // Boolean Exhaustion
	{nil, "(¬B→¬A)→(A→B)", pr.Classical, pr.NoModality},                   // ¬-Contraposition RL
	{nil, "¬(A∧B)→(¬A∨¬B)", pr.Classical, pr.NoModality},                  // Distribution of ¬∧ OI-∨
	{nil, "(¬¬A→¬¬B)→(A→B)", pr.Classical, pr.NoModality},                 // Double Contraposition RL
	{nil, "((A→(B→C))→A)→A", pr.Classical, pr.NoModality},                 // Shifted Peirce's Law
	{nil, "((A↔B)↔(A↔C))↔(B↔C)", pr.Classical, pr.NoModality},             // Iseki's Axiom 1
	{nil, "(A↔(B↔C))↔((A↔B)↔C)", pr.Classical, pr.NoModality},             // Iseki's Axiom 2
	{nil, "A↔((B↔(C↔A))↔(B↔C))", pr.Classical, pr.NoModality},             // Kalman's Axiom
	{nil, "A↔(((A↔B)↔(B↔C))↔C)", pr.Classical, pr.NoModality},             // XCB Axiom
	{nil, "¬(A↔B)→(¬(A→B)∨¬(B→A))", pr.Classical, pr.NoModality},          // Distribution of ¬↔ OI-∨
	{nil, "(A→(B∨C))→((A→B)∨(A→C))", pr.Classical, pr.NoModality},         // Distribution of →(∨) LR
	{nil, "((A→B)→C)→(((B→A)→C)→C)", pr.Classical, pr.NoModality},         // Dummett's LC, Wajsberg Linearity
	{nil, "((A→B)→C)→((C→A)→(D→A))", pr.Classical, pr.NoModality},         // Łukasiewicz's Axiom
	{nil, "(¬A→(B∨C))→((¬A→B)∨(¬A→C))", pr.Classical, pr.NoModality},      // Harrop's Rule
	{nil, "(A∧B)∨((A∧¬B)∨((¬A∧B)∨(¬A∧¬B)))", pr.Classical, pr.NoModality}, // Truth-Table Exhaustion

	// == 1st-Order Quantificational Theorems ==
	// P1QL...
	{nil, "∀u(Au∧B)→(∀uAu∧B)", pr.Positive, pr.NoModality},                        // Confinement of ∀∧ OI
	{nil, "(∀uAu∧B)→∀u(Au∧B)", pr.Positive, pr.NoModality},                        // Confinement of ∀∧ IO
	{nil, "(∀uAu∨B)→∀u(Au∨B)", pr.Positive, pr.NoModality},                        // Confinement of ∀∨ IO
	{nil, "∃u(Au∧B)→(∃uAu∧B)", pr.Positive, pr.NoModality},                        // Confinement of ∃∧ OI
	{nil, "(∃uAu∧B)→∃u(Au∧B)", pr.Positive, pr.NoModality},                        // Confinement of ∃∧ IO
	{nil, "∃u(Au∨B)→(∃uAu∨B)", pr.Positive, pr.NoModality},                        // Confinement of ∃∨ OI
	{nil, "(∃uAu∨B)→∃u(Au∨B)", pr.Positive, pr.NoModality},                        // Confinement of ∃∨ IO
	{nil, "∀u(B→Au)→(B→∀uAu)", pr.Positive, pr.NoModality},                        // Confinement of ∀→ OI-∀R
	{nil, "(B→∀uAu)→∀u(B→Au)", pr.Positive, pr.NoModality},                        // Confinement of ∀→ IO-∀R
	{nil, "∀u(Au→B)→(∃uAu→B)", pr.Positive, pr.NoModality},                        // Confinement of ∀→ OI-∃L
	{nil, "(∃uAu→B)→∀u(Au→B)", pr.Positive, pr.NoModality},                        // Confinement of ∀→ IO-∃L
	{nil, "∃u(Au→B)→(∀uAu→B)", pr.Positive, pr.NoModality},                        // Confinement of ∃→ OI-∀L
	{nil, "∃u(A→Bu)→(A→∃uBu)", pr.Positive, pr.NoModality},                        // Confinement of ∃→ OI-∃R
	{nil, "(A→∃uBu)→∃u(A→Bu)", pr.Positive, pr.NoModality},                        // Confinement of ∃→ IO-∃R
	{nil, "∀u(Au∧Bu)→(∀uAu∧∀uBu)", pr.Positive, pr.NoModality},                    // Distribution of ∀∧ OI
	{nil, "(∀uAu∧∀uBu)→∀u(Au∧Bu)", pr.Positive, pr.NoModality},                    // Distribution of ∀∧ IO
	{nil, "∃u(Au∨Bu)→(∃uAu∨∃uBu)", pr.Positive, pr.NoModality},                    // Distribution of ∃∧ OI
	{nil, "(∃uAu∨∃uBu)→∃u(Au∨Bu)", pr.Positive, pr.NoModality},                    // Distribution of ∃∧ IO
	{nil, "(∀uAu∨∀uBu)→∀u(Au∨Bu)", pr.Positive, pr.NoModality},                    // Distribution of ∀∨ IO (no OI)
	{nil, "∃u(Au∧Bu)→(∃uAu∧∃uBu)", pr.Positive, pr.NoModality},                    // Distribution of ∃∨ OI (no IO)
	{nil, "∀u(Au→Bu)→(∀uAu→∀uBu)", pr.Positive, pr.NoModality},                    // Distribution of ∀→ OI-∀ (no IO)
	{nil, "∀u(Au→Bu)→(∃uAu→∃uBu)", pr.Positive, pr.NoModality},                    // Distribution of ∀→ OI-∃ (no IO)
	{nil, "∃u(Au→Bu)→(∀uAu→∃uBu)", pr.Positive, pr.NoModality},                    // Distribution of ∃→ OI
	{nil, "(∃uAu→∀uBu)→∀u(Au→Bu)", pr.Positive, pr.NoModality},                    // Distribution of ∀→ IO-∃∀ (no OI)
	{nil, "(∀u(Au→Bu)∧∃u(Cu∧Au))→∃u(Cu∧Bu)", pr.Positive, pr.NoModality},          // Darii (AII - 1st Fig.)
	{nil, "(∀u(Au→Bu)∧∀u(Bu→Cu))→∀u(Au→Cu)", pr.Positive, pr.NoModality},          // Barbara (AAA - 1st Fig.)
	{nil, "(∃u(Au∧Bu)∧∀u(Au→Cu))→∃u(Cu∧Bu)", pr.Positive, pr.NoModality},          // Disamis (IAI - 3rd Fig.)
	{nil, "(∀u(Au→Bu)∧∃u(Au∧Cu))→∃u(Cu∧Bu)", pr.Positive, pr.NoModality},          // Datisi (AII - 3rd. Figure)
	{nil, "(∃u(Au∧Bu)∧∀u(Bu→Cu))→∃u(Cu∧Au)", pr.Positive, pr.NoModality},          // Dimaris (IAI - 4th Fig.)
	{nil, "(∀u(Au→¬Bu)∧∀u(Cu→Au))→∀u(Cu→¬Bu)", pr.Positive, pr.NoModality},        // Celarent (EAE - 1st Fig.)
	{nil, "(∀u(Au→¬Bu)∧∃u(Cu∧Au))→∃u(Cu∧¬Bu)", pr.Positive, pr.NoModality},        // Ferio (EIO - 1st Fig.)
	{nil, "(∀u(Au→¬Bu)∧∃u(Au∧Cu))→∃u(Cu∧¬Bu)", pr.Positive, pr.NoModality},        // Ferison (EIO - 3rd Fig.)
	{nil, "(∀u(Au→Bu)∧∀u(Au→Cu))→(∃uAu→∃u(Bu∧Cu))", pr.Positive, pr.NoModality},   // Darapti (AAI - 3rd Fig.)
	{nil, "(∀u(Au→Bu)∧∀u(Bu→Cu))→(∃uAu→∃u(Bu∧Cu))", pr.Positive, pr.NoModality},   // Bramantip (AAI - 4th Fig.)
	{nil, "(∀u(Au→¬Bu)∧∀u(Au→Cu))→(∃uAu→∃u(Cu∧¬Bu))", pr.Positive, pr.NoModality}, // Felapton (EAO - 3rd Fig.)
	// M1QL...
	{nil, "¬∃uAu→∀u¬Au", pr.Minimal, pr.NoModality},                              // Distribution of ¬∃ OI
	{nil, "∀u¬Au→¬∃uAu", pr.Minimal, pr.NoModality},                              // Distribution of ¬∃ IO
	{nil, "∃u¬Au→¬∀uAu", pr.Minimal, pr.NoModality},                              // Distribution of ¬∀ IO
	{nil, "(∀u(Au→¬Bu)∧∀u(Cu→Bu))→∀u(Cu→¬Au)", pr.Minimal, pr.NoModality},        // Cesare (EAE - 2nd Fig.)
	{nil, "(∀u(Au→Bu)∧∀u(Cu→¬Bu))→∀u(Cu→¬Au)", pr.Minimal, pr.NoModality},        // Camestres (AEE - 2nd Fig.)
	{nil, "(∀u(Au→¬Bu)∧∃u(Cu∧Bu))→∃u(Cu∧¬Au)", pr.Minimal, pr.NoModality},        // Festino (EIO - 2nd Fig.)
	{nil, "(∀u(Au→Bu)∧∃u(Cu∧¬Bu))→∃u(Cu∧¬Au)", pr.Minimal, pr.NoModality},        // Baroco (AOO - 2nd Fig.)
	{nil, "(∀u(Au→¬Bu)∧∃u(Bu∧Cu))→∃u(Cu∧¬Au)", pr.Minimal, pr.NoModality},        // Presison (EIO - 4th Fig.)
	{nil, "(∀u(Au→Bu)∧∀u(Bu→¬Au))→(∃uAu→∀u(Cu→¬Au))", pr.Minimal, pr.NoModality}, // Camenes (AEE - 4th Fig.)
	{nil, "(∀u(Au→¬Bu)∧∀u(Bu→Cu))→(∃uBu→∃u(Cu∧¬Au))", pr.Minimal, pr.NoModality}, // Fesapo (EAO - 4th Fig.)
	// C1QL...
	{nil, "¬∀uAu→∃u¬Au", pr.Classical, pr.NoModality},           // Distribution of ¬∀ OI
	{nil, "∃u(Au→∀vAv)", pr.Classical, pr.NoModality},           // The Drinker Paradox →∀
	{nil, "∀u(Au∨B)→(∀uAu∨B)", pr.Classical, pr.NoModality},     // Confinement of ∀∨ OI
	{nil, "(∀uAu→B)→∃u(Au→B)", pr.Classical, pr.NoModality},     // Confinement of ∃→ IO-∀L
	{nil, "(∀uAu→∃uBu)→∃u(Au→Bu)", pr.Classical, pr.NoModality}, // Distribution of ∃→ IO

	// == Identity Logic Theorems ==
	// TNLi...
	{nil, "a=b→b=a", pr.Implicational, pr.NoModality},       // Identity Symmetry
	{nil, "Aa→(a=b→Ab)", pr.Implicational, pr.NoModality},   // 1st-Order Indiscernibility
	{nil, "a=b→(b=c→a=c)", pr.Implicational, pr.NoModality}, // Identity Transitivity
	{nil, "a=b→(Aac→Abc)", pr.Implicational, pr.NoModality}, // Relational Indiscernibility L
	{nil, "a=b→(Aca→Acb)", pr.Implicational, pr.NoModality}, // Relational Indiscernibility R
	// PNLi...
	{nil, "a=b→(Aa↔Ab)", pr.Positive, pr.NoModality}, // Indiscernibility of Identicals Instance

	// == Second-Order Logic Theorems ==
	// P2QL...
	{nil, "∀U∀uUu→∀uAu", pr.Positive, pr.NoModality},         // Universal Predicate Instantiation
	{nil, "Aa→∃UUa", pr.Positive, pr.NoModality},             // Existential Predicate Generalization
	{nil, "(∀U(Ua→Ub)∧Aa)→Ab", pr.Positive, pr.NoModality},   // 2nd-Order Indiscernibility
	{nil, "∀u∀v(u=v→∀U(Uu↔Uv))", pr.Positive, pr.NoModality}, // Indiscernibility of Identicals

	// == Propositional Modal Logic Theorems ==
	// PPL+K...
	{nil, "□(A∧B)→(□A∧□B)", pr.Positive, pr.ModalK}, // Distribution of □∧ OI
	{nil, "(□A∧□B)→□(A∧B)", pr.Positive, pr.ModalK}, // Distribution of □∧ IO
	{nil, "(□A∨□B)→□(A∨B)", pr.Positive, pr.ModalK}, // Distribution of □∨ IO (no OI)
	{nil, "◇(A→B)→(□A→◇B)", pr.Positive, pr.ModalK}, // Distribution of ◇→ OI
	{nil, "□(A→B)→(□A→□B)", pr.Positive, pr.ModalK}, // CK Axiom 1
	{nil, "□(A→B)→(◇A→◇B)", pr.Positive, pr.ModalK}, // CK Axiom 2
	{nil, "◇(A∧B)→(◇A∧◇B)", pr.Positive, pr.ModalK}, // Distribution of ◇∧ OI (no IO)
	{nil, "(◇A∨◇B)→◇(A∨B)", pr.Positive, pr.ModalK}, // Distribution of ◇∨ IO
	// MPL+K...
	{nil, "¬◇⊥", pr.Minimal, pr.ModalK},     // WK Axiom 1
	{nil, "¬◇A→□¬A", pr.Minimal, pr.ModalK}, // Distribution of ¬◇ OI
	{nil, "□¬A→¬◇A", pr.Minimal, pr.ModalK}, // Distribution of ¬◇ IO
	// CPL+K...
	{nil, "◇(A∨B)→(◇A∨◇B)", pr.Classical, pr.ModalK}, // Distribution of ◇∨ OI (IK Axiom 1)
	{nil, "(◇A→□B)→□(A→B)", pr.Classical, pr.ModalK}, // Distribution of □→ IO (IK Axiom 2, no OI)
	{nil, "(□A→◇B)→◇(A→B)", pr.Classical, pr.ModalK}, // Distribution of ◇→ IO
	// PPL+D...
	{nil, "□A→◇A", pr.Positive, pr.ModalD}, // ElimD (Seriality)
	// PPL+M...
	{nil, "□A→A", pr.Positive, pr.ModalM},   // ElimM (Reflexivity)
	{nil, "A→◇A", pr.Positive, pr.ModalM},   // IntroM (Reflexivity)
	{nil, "□□A→□A", pr.Positive, pr.ModalM}, // Weak □-Transitivity
	{nil, "◇A→◇◇A", pr.Positive, pr.ModalM}, // Weak ◇-Transitivity
	// PPL+4...
	{nil, "□A→□□A", pr.Positive, pr.Modal4}, // Intro4
	{nil, "◇◇A→◇A", pr.Positive, pr.Modal4}, // Elim4
	// PPL+B
	{nil, "A→□◇A", pr.Positive, pr.ModalB}, // IntroB
	{nil, "◇□A→A", pr.Positive, pr.ModalB}, // ElimB
	// PPL+KD...
	{nil, "□(□A→◇A)", pr.Positive, pr.ModalKD}, // Necessity of Seriality
	// PPL+K4B...
	{nil, "◇A→□◇A", pr.Positive, pr.ModalK4B}, // Euclideanism (K5) with K4B
	{nil, "◇□A→□A", pr.Positive, pr.ModalK4B}, // Euclideanism (K5) with K4B

	// == 1st-Order Quantificational Modal Logic Theorems ==
	// P1QL+K...
	{nil, "□∀uAu→∀u□Au", pr.Positive, pr.ModalK}, // Converse Barcan Formula (□∀ to ∀□)
	{nil, "∃u◇Au→◇∃uAu", pr.Positive, pr.ModalK}, // Converse Barcan Formula (∃◇ to ◇∃)
}

func TestNDTheorems(t *testing.T) {
	var (
		tc      testCase
		wffG    *fmla.Wff
		wffsP   []*fmla.Wff
		drv     *Deriver
		s, name string
	)

	for _, tc = range tcs {
		wffsP, wffG = ndTestParseWffs(t, tc.prems...), ndTestParseWff(t, tc.goal)

		drv = NewDeriver(tc.infS, tc.modS, wffG, wffsP...)

		if !drv.DeriveAtStrength() {
			s = drv.Prf.ConvertToFitchString()

			t.Logf("\n%s", s)

			name = pr.NameLogic(drv.InfS, drv.SynB, drv.ModS)

			t.Fatalf("FAILED! Did not derive %q from %q in %s.", tc.goal, tc.prems, name)
		}

		drv.Prf = drv.Prf.MinimizeProof()

		s = drv.Prf.ConvertToFitchString()

		name = pr.NameLogic(drv.InfS, drv.SynB, drv.ModS)

		t.Logf("\nPASSED! %q ⊢ %q in %s:\n%s", tc.prems, tc.goal, name, s)
	}

	t.Logf("All %d tests passed!\n", len(tcs))
}

func TestWeakestNDTheorems(t *testing.T) {
	var (
		tc        testCase
		wffG      *fmla.Wff
		wffsP     []*fmla.Wff
		drvsW     []*Deriver
		drv, drvW *Deriver
		s, name   string
	)

TESTWEAKESTTHEOREMS_OUTER:
	for _, tc = range tcs {
		wffsP, wffG = ndTestParseWffs(t, tc.prems...), ndTestParseWff(t, tc.goal)

		drv = NewDeriver(tc.infS, tc.modS, wffG, wffsP...)

		if !drv.DeriveAtStrength() {
			s = drv.Prf.ConvertToFitchString()

			t.Logf("\n%s", s)

			name = pr.NameLogic(drv.InfS, drv.SynB, drv.ModS)

			t.Fatalf("FAILED! Did not derive %q from %q in %s.", tc.goal, tc.prems, name)
		}

		t.Logf("Testing for weakest proof of %q...\n", fmla.GetWffString(wffG))

		drvsW = DeriveAtWeakestStrengths(wffG, wffsP...)

		for _, drvW = range drvsW {
			if drvW.InfS == tc.infS && drvW.ModS == tc.modS {
				t.Log("PASSED! Strengths matched for two proofs!")

				// drv.Prf, drvW.Prf = drv.Prf.MinimizeProof(), drvW.Prf.MinimizeProof()

				// s = drv.Prf.ConvertToFitchString() + "\n\n" + drvW.Prf.ConvertToFitchString()

				// t.Log(s)

				continue TESTWEAKESTTHEOREMS_OUTER
			}
		}

		t.Logf("FAILED!\n")

		drv.Prf = drv.Prf.MinimizeProof()

		s = drv.Prf.ConvertToFitchString()

		name = pr.NameLogic(drv.InfS, drv.SynB, drv.ModS)

		t.Logf("The test-case proof passed in %s:\n%s\n\n", name, s)

		for _, drvW = range drvsW {
			drvW.Prf = drvW.Prf.MinimizeProof()

			s = drvW.Prf.ConvertToFitchString()

			name = pr.NameLogic(drvW.InfS, drvW.SynB, drvW.ModS)

			t.Logf("But this proof passed in %s:\n%s\n\n", name, s)
		}

		t.Fatal()
	}
}
