package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
)

func distributeLine(ln *pr.Line, inf pr.InfSt, mod pr.ModSt) (tot int) {
	var (
		rule                                                pr.NDRule
		prf                                                 *pr.Prf
		wff, subL, subR, subA, subB, subC, newL, newR, newG *fmla.Wff
	)

	if rule = ln.Rule(); !(rule == pr.Prem || rule == pr.Ass || pr.IsDischargeRule(rule)) {
		goto DISTRIBUTELINE_END
	}

	switch prf, wff = ln.Prf(), ln.Wff(); wff.Mop() {
	case fmla.To: // W is A→B.
		subL, subR, _ = wff.Subs()

		if subL.Kind() == fmla.Binary {
			subA, subB, subC = subL.SubL(), subL.SubR(), subR

			switch subL.Mop() {
			case fmla.To: // W is (A→B)→C.
				if pr.NoInference < inf { // At least TPL.
					// (A→B)→C ⊢TPL B→(A→B),B→C.
					newR = fmla.NewBinaryWff(fmla.To, subA, subB)
					newG = fmla.NewBinaryWff(fmla.To, subB, newR)

					tot += goalAssume(prf, newG, pr.Implicational, mod)

					newG = fmla.NewBinaryWff(fmla.To, subB, subC)

					tot += goalAssume(prf, newG, pr.Implicational, mod)
				}

				if pr.Minimal < inf { // At least IPL.
					// (A→B)→C ⊢IPL ¬A→(A→B),¬A→C.
					newL = fmla.NewUnaryWff(fmla.Neg, subA)
					newG = fmla.NewBinaryWff(fmla.To, subA, subB)
					newG = fmla.NewBinaryWff(fmla.To, newL, newG)

					tot += goalAssume(prf, newG, pr.Intuitionistic, mod)

					newL = fmla.NewUnaryWff(fmla.Neg, subA)
					newG = fmla.NewBinaryWff(fmla.To, newL, subC)

					tot += goalAssume(prf, newG, pr.Intuitionistic, mod)
				}
			case fmla.Vee: // W is (A∨B)→C.
				if pr.Implicational < inf { // At least PPL.
					// (A∨B)→C ⊢PPL A→C,B→C.
					newG = fmla.NewBinaryWff(fmla.To, subA, subC)

					tot += goalAssume(prf, newG, pr.Positive, mod)

					newG = fmla.NewBinaryWff(fmla.To, subB, subC)

					tot += goalAssume(prf, newG, pr.Positive, mod)
				}
			case fmla.Wedge: // W is (A∧B)→C.
				if pr.Implicational < inf { // At least PPL.
					// (A∧B)→C ⊢PPL A→(B→C).
					newR = fmla.NewBinaryWff(fmla.To, subB, subC)
					newG = fmla.NewBinaryWff(fmla.To, subA, newR)

					tot += goalAssume(prf, newG, pr.Positive, mod)
				}
			case fmla.Iff: // W is (A↔B)→C.
				if pr.Implicational < inf { // At least PPL.
					// (A↔B)→C ⊢PPL (A→B)→((B→A)→C).
					newL = fmla.NewBinaryWff(fmla.To, subA, subB)

					newR = fmla.NewBinaryWff(fmla.To, subB, subA)
					newR = fmla.NewBinaryWff(fmla.To, newR, subC)

					newG = fmla.NewBinaryWff(fmla.To, newL, newR)

					tot += goalAssume(prf, newG, pr.Positive, mod)
				}
			}
		} else if subL.Kind() == fmla.Unary {
			subA, subB = subL, subR

			switch subL.Mop() {
			case fmla.Neg: // W is ¬A→B.
				if pr.Positive < inf { // At least MPL.
					if subA.SubL().Mop() == fmla.Neg { // W is ¬¬A→B.
						// ¬¬A→B ⊢MPL A→¬¬A,A→B.
						newL = subA.Locate("LL")

						newG = fmla.NewBinaryWff(fmla.To, newL, subA)

						tot += goalAssume(prf, newG, pr.Minimal, mod)

						newG = fmla.NewBinaryWff(fmla.To, newL, subB)

						tot += goalAssume(prf, newG, pr.Minimal, mod)
					}
				}
			}
		}

		if subR.Kind() == fmla.Binary {
			subA, subB, subC = subL, subR.SubL(), subR.SubR()

			switch subR.Mop() {
			case fmla.To: // W is A→(B→C).
				if pr.NoInference < inf { // At least TPL.
					// A→(B→C) ⊢TPL B→(A→C).
					newG = fmla.NewBinaryWff(fmla.To, subA, subC)
					newG = fmla.NewBinaryWff(fmla.To, subB, newG)

					tot += goalAssume(prf, newG, pr.Implicational, mod)
				}
			case fmla.Vee: // W is A→(B∨C).
				if pr.Intuitionistic < inf { // At least JPL.
					if subB.Mop() == fmla.Neg || subC.Mop() == fmla.Neg { // W is A→(¬B∨C) or A→(B∨¬C).
						// A→(¬B∨C) ⊢JPL (A→¬B)∨(A→C); A→(B∨¬C) ⊢JPL (A→B)∨(A→¬C).
						newL = fmla.NewBinaryWff(fmla.To, subA, subB)
						newR = fmla.NewBinaryWff(fmla.To, subA, subC)

						newG = fmla.NewBinaryWff(fmla.Vee, newL, newR)

						tot += goalAssume(prf, newG, pr.Jankov, mod)
					} else if pr.Jankov < inf { // At least GPL.
						// A→(B∨C) ⊢GPL (A→B)∨(A→C).
						newL = fmla.NewBinaryWff(fmla.To, subA, subB)
						newR = fmla.NewBinaryWff(fmla.To, subA, subC)

						newG = fmla.NewBinaryWff(fmla.Vee, newL, newR)

						tot += goalAssume(prf, newG, pr.GödelDummett, mod)
					}
				}
			case fmla.Wedge: // W is A→(B∧C).
				if pr.Implicational < inf { // At least PPL.
					// A→(B∧C) ⊢PPL A→B,A→C.
					newG = fmla.NewBinaryWff(fmla.To, subA, subB)

					tot += goalAssume(prf, newG, pr.Positive, mod)

					newG = fmla.NewBinaryWff(fmla.To, subA, subC)

					tot += goalAssume(prf, newG, pr.Positive, mod)
				}
			case fmla.Iff: // W is A→(B↔C).
				if pr.Implicational < inf { // At least PPL.
					// A→(B↔C) ⊢PPL A→(B→C),A→(C→B).
					newR = fmla.NewBinaryWff(fmla.To, subB, subC)
					newG = fmla.NewBinaryWff(fmla.To, subA, newR)

					tot += goalAssume(prf, newG, pr.Positive, mod)

					newR = fmla.NewBinaryWff(fmla.To, subC, subB)
					newG = fmla.NewBinaryWff(fmla.To, subA, newR)

					tot += goalAssume(prf, newG, pr.Positive, mod)
				}
			}
		} else if subR.Kind() == fmla.Unary {
			subA, subB = subL, subR

			switch subR.Mop() {
			case fmla.Neg: // W is A→¬B.
				if pr.Positive < inf { // At least MPL.
					// A→¬B ⊢MPL B→¬A.
					newL, newR = subB.SubL(), fmla.NewUnaryWff(fmla.Neg, subA)

					newG = fmla.NewBinaryWff(fmla.To, newL, newR)

					tot += goalAssume(prf, newG, pr.Minimal, mod)
				}
			}
		}
	case fmla.Neg: // W is ¬A.
		subL = wff.SubL()

		if subL.Kind() == fmla.Binary {
			subA, subB, _ = subL.Subs()

			switch subL.Mop() {
			case fmla.To: // W is ¬(A→B).
				if pr.Positive < inf { // At least MPL.
					// ¬(A→B) ⊢MPL ¬B.
					newG = fmla.NewUnaryWff(fmla.Neg, subB)

					tot += goalAssume(prf, newG, pr.Minimal, mod)
				}

				if pr.Minimal < inf { // At least IPL.
					// ¬(A→B) ⊢IPL ¬¬A.
					newG = fmla.NewUnaryWff(fmla.Neg, fmla.NewUnaryWff(fmla.Neg, subA))

					tot += goalAssume(prf, newG, pr.Intuitionistic, mod)
				}
			case fmla.Vee: // W is ¬(A∨B).
				if pr.Positive < inf { // At least MPL.
					// ¬(A∨B) ⊢MPL ¬A,¬B.
					newG = fmla.NewUnaryWff(fmla.Neg, subA)

					tot += goalAssume(prf, newG, pr.Minimal, mod)

					newG = fmla.NewUnaryWff(fmla.Neg, subB)

					tot += goalAssume(prf, newG, pr.Minimal, mod)
				}
			case fmla.Wedge: // W is ¬(A∧B).
				if pr.Positive < inf { // At least MPL.
					// ¬(A∧B) ⊢MPL A→¬B.
					newL = fmla.NewUnaryWff(fmla.Neg, subB)

					newG = fmla.NewBinaryWff(fmla.To, subA, newL)

					tot += goalAssume(prf, newG, pr.Minimal, mod)
				}
			case fmla.Iff: // W is ¬(A↔B).
				if pr.Positive < inf { // At least MPL.
					// ¬(A↔B) ⊢MPL A→¬B.
					newL = fmla.NewUnaryWff(fmla.Neg, subB)

					newG = fmla.NewBinaryWff(fmla.To, subA, newL)

					tot += goalAssume(prf, newG, pr.Minimal, mod)
				}
			}
		} else if subL.Kind() == fmla.Unary {
			switch subL.Mop() {
			case fmla.Neg: // W is ¬¬A.
				if subL.SubL().Mop() == fmla.Neg { // W is ¬¬¬A.
					// ¬¬¬A ⊢MPL ¬A.
					newG = fmla.NewUnaryWff(fmla.Neg, subL.Locate("LL"))

					tot += goalAssume(prf, newG, pr.Minimal, mod)
				} else if subL.SubL().Kind() == fmla.Binary {
					subA, subB, _ = subL.SubL().Subs()

					switch subL.SubL().Mop() {
					case fmla.To: // W is ¬¬(A→B).
						if pr.Positive < inf { // At least MPL.
							// ¬¬(A→B) ⊢MPL ¬B→¬A.
							newL, newR = fmla.NewUnaryWff(fmla.Neg, subB), fmla.NewUnaryWff(fmla.Neg, subA)

							newG = fmla.NewBinaryWff(fmla.To, newL, newR)

							tot += goalAssume(prf, newG, pr.Minimal, mod)
						}
					case fmla.Vee: // W is ¬¬(A∨B).
						if pr.Positive < inf { // At least MPL.
							// ¬¬(A∨B) ⊢MPL ¬A→¬¬B.
							newL, newR = fmla.NewUnaryWff(fmla.Neg, subA), fmla.NewUnaryWff(fmla.Neg, fmla.NewUnaryWff(fmla.Neg, subB))

							newG = fmla.NewBinaryWff(fmla.To, newL, newR)

							tot += goalAssume(prf, newG, pr.Minimal, mod)
						}
					case fmla.Wedge: // W is ¬¬(A∧B).
						if pr.Positive < inf { // At least MPL.
							// ¬¬(A∧B) ⊢MPL ¬¬A,¬¬B.
							newG = fmla.NewUnaryWff(fmla.Neg, fmla.NewUnaryWff(fmla.Neg, subA))

							tot += goalAssume(prf, newG, pr.Minimal, mod)

							newG = fmla.NewUnaryWff(fmla.Neg, fmla.NewUnaryWff(fmla.Neg, subB))

							tot += goalAssume(prf, newG, pr.Minimal, mod)
						}
					case fmla.Iff: // W is ¬¬(A↔B).
						if pr.Positive < inf { // At least MPL.
							// ¬¬(A↔B) ⊢MPL ¬A↔¬B.
							newL, newR = fmla.NewUnaryWff(fmla.Neg, subA), fmla.NewUnaryWff(fmla.Neg, subB)

							newG = fmla.NewBinaryWff(fmla.Iff, newL, newR)

							tot += goalAssume(prf, newG, pr.Minimal, mod)
						}
					}
				}

			}
		}
	}

DISTRIBUTELINE_END:
	return
}
