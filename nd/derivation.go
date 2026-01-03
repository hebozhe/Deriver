package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
)

type Derivation struct {
	Prf     *pr.Proof
	InfS    InferStrength
	ModS    ModalStrength
	MetGoal bool
}

func pumpIntroductions(prf *pr.Proof, iFuncs []ndRuleFunc) (added uint, met bool) {
	var (
		iFunc  ndRuleFunc
		prfsI  []*pr.Proof
		prfI   *pr.Proof
		addedI uint
	)

	if _, _, met = prf.HeadGoalMet(); !met {
		for _, iFunc = range iFuncs {
			added += iFunc(prf)
		}

		prfsI = collectInnerProofs(prf)

		for _, prfI = range prfsI {
			addedI, _ = pumpIntroductions(prfI, iFuncs)

			added += addedI
		}

		_, _, met = prf.HeadGoalMet()
	}

	return
}

func pumpEliminations(prf *pr.Proof, eFuncs []ndRuleFunc) (added uint, met bool) {
	var (
		eFunc  ndRuleFunc
		prfsI  []*pr.Proof
		prfI   *pr.Proof
		addedI uint
	)

	if _, _, met = prf.HeadGoalMet(); !met {
		for _, eFunc = range eFuncs {
			added += eFunc(prf)
		}

		prfsI = collectInnerProofs(prf)

		for _, prfI = range prfsI {
			addedI, _ = pumpEliminations(prfI, eFuncs)

			added += addedI
		}

		_, _, met = prf.HeadGoalMet()
	}

	return
}

func Derive(goal *fmla.WffTree, prems ...*fmla.WffTree) (drv *Derivation) {
	var (
		prf            *pr.Proof
		infS           InferStrength
		modS           ModalStrength
		iFuncs, eFuncs []ndRuleFunc
		added          uint
		met            bool
	)

	infS, modS = Implicational, SystemK

	prf = pr.NewBaseProof(goal, prems...)

	iFuncs, eFuncs = ruleFuncsByStrengths(infS, modS)

	for {
		// 1. Apply introduction rules until no unique lines are produced or the head goal is met.
		// 2. If (1) met the head goal, exit! If new, unique lines are produced,
		//    pop subgoals and return to (1). Otherwise, move to (3).
		if added, met = pumpIntroductions(prf, iFuncs); met {
			break
		} else if 0 < added {
			_ = prf.PopMetSubgoals()

			continue
		}

		// 3. Continue applying elimination rules until no unique lines are produced or the head goal is met.
		// 4. If (3) met the head goal, exit! If new, unique lines are produced,
		//    pop subgoals and return to (1). Otherwise, move to (5).
		if added, met = pumpEliminations(prf, eFuncs); met {
			break
		} else if 0 < added {
			_ = prf.PopMetSubgoals()

			continue
		}

		// 5. Create inner proofs to facilitate both introduction and elimination rules.
		// 6. If (5) produced new, unique inner proofs, return to (1).
		//    Otherwise, move to (7).
		if added = seedInnerIntroProofs(prf) + seedInnerElimProofs(prf); 0 < added {
			continue
		}

		// 7. Increment the modal strength; or, if it's already at KD4B, increment the inferential strength,
		//    reset the modal strength to K. If the modal strength is already at Classical KD4B, exit in failure!
		//    Otherwise, return to (1).
		if infS == Classical && modS == SystemKD4B {
			break
		}

		if modS == incModalStrength(modS) {
			infS, modS = incInferStrength(infS), SystemK
		} else {
			modS = incModalStrength(modS)
		}
	}

	drv = &Derivation{
		Prf:     prf,
		InfS:    infS,
		ModS:    modS,
		MetGoal: met,
	}

	return
}
