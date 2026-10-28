package pr

type NDRule uint8

// Note: DO NOT adjust the order of these rules,
// as they will play a part in determining the kind of logic
// that is needed to derive a given theorem.
const (
	NoRule NDRule = iota // This is a non-rule.
	Solve                // This is a vacuous purpose for the base proof.
	Prem
	// Assumpions
	Ass
	// Implicational Propositional Logic (TPL)
	TopI // ⊢TPL ⊤
	ToI  // [A…B]→I ⊢TPL A→B
	ToE  // A→B,A ⊢TPL B
	Reit // A,[…](→I|¬I|∀I|∃E) ⊢TPL […A](→I|¬I|∀I|∃E)
	Thm  // [⊤…A]Thm ⊢TPL A
	// Positive Propositional Logic (PPL)
	WedgeI // A,B ⊢PPL A∧B
	WedgeE // A∧B ⊢PPL B; A∧B ⊢PPL B
	VeeI   // A ⊢PPL A∨B; A ⊢PPL B∨A
	VeeE   // A∨B,A→C,B→C ⊢PPL C
	IffI   // A→B,B→A ⊢PPL A↔B
	IffE   // A↔B ⊢PPL A→B; A↔B ⊢PPL B→A
	// Minimal Propositional Logic (MPL)
	BotI // A,¬A ⊢MPL ⊥
	NegI // [A…⊥]¬I ⊢MPL ¬A
	// Intuitionistic Propositional Logic (IPL)
	BotE // ⊥ ⊢IPL A
	// Jankov Propositional Logic (JPL)
	Jan // ¬A→B,¬¬A→B ⊢JPL B
	// Gödel-Dummett Propositional Logic (GPL)
	Göd // (A→B)→C,(B→A)→C ⊢GPL C
	// Smetanich Propositional Logic (SPL)
	Sme // A→C,¬B→C,(A→B)→C ⊢SPL C
	// Classical Propositional Logic (CPL)
	NegE // ¬¬A ⊢CPL A
	// Implicational N-Order Logic with Identity (TNLi)
	EqualI // ⊢TNLi t=t
	EqualE // a=b,Φ(a) ⊢TNLi Φ(b/a)
	// Positive N-Order Quantification Logic (PQL)
	ForAllI // [⊤…Φ(a)]∀I ⊢P1QL ∀xΦ(x/a); [⊤…Φ(A)]∀I ⊢P2QL ∀XΦ(X/A)
	ForAllE // ∀xΦ(x) ⊢P1QL Φ(a/x); ∀XΦ(X) ⊢P2QL Φ(A/X)
	ExistsI // A(a) ⊢P1QL ∃xΦ(x/a); Φ(A) ⊢P2QL ∃XΦ(X/A)
	ExistsE // ∃xΦ(x),[Φ(t/x)…Ψ(~t~)]∃E ⊢P1QL Ψ; ∃XΦ(X),[Φ(T/X)…Ψ(~T~)]∃E ⊢P2QL Ψ
	// Positive Propositional Logic with Modality Ew, En, or Es (PPL+E*)
	BoxCon // If ⊢ A→B,B→A, then A→B,B→A ⊢PPL+Ew □A→□B
	DmdCon // If ⊢ A→B,B→A, then A→B,B→A ⊢PPL+Ew ◇A→◇B
	// Minimal Propositional Logic with Modality Ew (MPL+Ew)
	BoxIntEw // □⊤ ⊢MPL+Ew ¬◇⊥; □⊥ ⊢MPL+Ew ¬◇⊤
	DmdIntEw // ◇⊤ ⊢MPL+Ew ¬□⊥; ◇⊥ ⊢MPL+Ew ¬□⊤
	// Minimal Propositional Logic with Modality En (MPL+En)
	BoxIntEn // □A ⊢MPL+En ¬◇¬A; □¬A ⊢MPL+En ¬◇A
	DmdIntEn // ◇A ⊢MPL+En ¬□¬A; ◇¬A ⊢MPL+En ¬□A
	// Minimal Propositional Logic with Modality Es (MPL+Es)
	BoxIntEs // If ⊢ A→¬B, □A,A→¬B ⊢MPL+Es ¬◇B
	DmdIntEs // If ⊢ A→¬B, ◇A,A→¬B ⊢MPL+Es ¬□B
	// Classical Propositional Logic with Modality Ew, En or Es (CPL+E*)
	DmdI // ¬□¬A ⊢CPL+Ew ◇A
	// Positive Propositional Logic with Modality M (PPL+M)
	BoxMon // If ⊢ A→B, then A→B ⊢PPL+M □A→□B
	DmdMon // If ⊢ A→B, then A→B ⊢PPL+M ◇A→◇B
	BoxE   // □A,[A…B]□E ⊢PPL+M □B
	DmdE   // ◇A,[A…B]◇E ⊢PPL+M ◇B
	// Positive Propositional Logic with Modality N (PPL+N)
	BoxI // [⊤…A]□I ⊢PPL+N □A
	// Minimal Propositional Logic with Modality N (MPL+N)
	NegDmdI // [⊤…¬A]¬◇I ⊢MPL+N ¬◇A
	// Positive Propositional Logic with Modality C (PPL+C)
	BoxAgg // □A,□B ⊢PPL+C □(A∧B)
	ReitC  // □A,[…](□E|□I) ⊢PPL+C […A](□E|□I)
	// Positive Propositional Logic with Modality K (PPL+K)
	ReitK // □A,[…]◇E ⊢PPL+K […A]◇E
	// Positive Propositional Logic with Modality D (PPL+D)
	RuleD // □A ⊢PPL+D ◇A
	// Positive Propositional Logic with Modality T (PPL+T)
	IntroT // A ⊢PPL+T ◇A
	ElimT  // □A ⊢PPL+T A
	// Positive Propositional Logic with Modality 4 (PPL+4)
	Intro4 // □A ⊢PPL+4 □□A
	Elim4  // ◇◇A ⊢PPL+4 ◇A
	// Positive Propositional Logic with Modality B (PPL+B)
	IntroB // A ⊢PPL+B □◇A
	ElimB  // ◇□A ⊢PPL+B A
	// Positive Propositional Logic with Modality 5 (PPL+5)
	Intro5 // ◇A ⊢PPL+5 □◇A
	Elim5  // ◇□A ⊢PPL+5 □A
)

var reqJustCounts map[NDRule]int = map[NDRule]int{
	// Propositional logics:
	ToI:  0,
	Thm:  0,
	NegI: 0,
	// Quantificational logics:
	ForAllI: 0,
	ExistsE: 1, // The line that has existential quantifier.
	// Modal logics:
	BoxE:    1,
	DmdE:    1,
	BoxI:    0,
	NegDmdI: 0,
}

var modalIncrement map[NDRule]int = map[NDRule]int{
	ToI:     0,
	Thm:     2,
	NegI:    0,
	ForAllI: 0,
	ExistsE: 0,
	BoxE:    1,
	DmdE:    1,
	BoxI:    1,
	NegDmdI: 1,
}

var rulePCount map[NDRule]int = map[NDRule]int{
	Prem:     0,
	TopI:     0,
	ToI:      2,
	ToE:      2,
	Reit:     1,
	Thm:      2,
	WedgeI:   2,
	WedgeE:   1,
	VeeI:     1,
	VeeE:     3,
	IffI:     2,
	IffE:     1,
	BotI:     2,
	NegI:     2,
	BotE:     1,
	Jan:      2,
	Göd:      2,
	Sme:      3,
	NegE:     1,
	EqualI:   0,
	EqualE:   2,
	ForAllI:  2,
	ForAllE:  1,
	ExistsI:  1,
	ExistsE:  3,
	BoxCon:   2,
	DmdCon:   2,
	BoxIntEw: 1,
	DmdIntEw: 1,
	BoxIntEn: 1,
	DmdIntEn: 1,
	BoxIntEs: 2,
	DmdIntEs: 2,
	DmdI:     1,
	BoxMon:   1,
	DmdMon:   1,
	BoxE:     3,
	DmdE:     3,
	BoxI:     2,
	NegDmdI:  2,
	BoxAgg:   2,
	ReitC:    1,
	ReitK:    1,
	RuleD:    1,
	IntroT:   1,
	ElimT:    1,
	Intro4:   1,
	Elim4:    1,
	IntroB:   1,
	ElimB:    1,
	Intro5:   1,
	Elim5:    1,
}

func justCountIsCorrect(rule, purp NDRule, lenJ int) (is bool) {
	var (
		lenC int
	)

	if rule == Ass {
		lenC, is = reqJustCounts[purp]

		is = is && lenJ == lenC
	} else {
		lenC = rulePCount[rule]

		is = lenJ == lenC
	}

	return
}

func IsDischargeRule(rule NDRule) (is bool) {
	_, is = reqJustCounts[rule]

	return
}
