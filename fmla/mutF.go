package fmla

import (
	"slices"
)

func replaceAllPreds(wffA *Wff, predA, predB Predicate) (wffB *Wff) {
	var (
		subL, subR *Wff
	)

	switch wffA.kind {
	case Atomic:
		if wffA.pred == predA {
			wffB = NewAtomicWff(predB, wffA.args...)
		} else {
			wffB = wffA.DeepCopy()
		}
	case Unary:
		subL = replaceAllPreds(wffA.subL, predA, predB)

		wffB = NewUnaryWff(wffA.mop, subL)
	case Binary:
		subL, subR = replaceAllPreds(wffA.subL, predA, predB), replaceAllPreds(wffA.subR, predA, predB)

		wffB = NewBinaryWff(wffA.mop, subL, subR)
	case Quantified:
		if wffA.pv == predA {
			wffB = wffA.DeepCopy()
		} else {
			subL = replaceAllPreds(wffA.subL, predA, predB)

			wffB = NewQuantifiedWff(wffA.mop, subL, wffA.pv, wffA.av)
		}
	}

	return
}

func replaceAllArgs(wffA *Wff, argA, argB Argument) (wffB *Wff) {
	var (
		subL, subR   *Wff
		arg          Argument
		valency, dex int
		argsB        []Argument
	)

	switch wffA.kind {
	case Atomic:
		if valency = len(wffA.args); 0 < valency && slices.Contains(wffA.args, argA) {
			argsB = make([]Argument, valency)

			for dex, arg = range wffA.args {
				if arg == argA {
					argsB[dex] = argB
				} else {
					argsB[dex] = arg
				}
			}

			wffB = NewAtomicWff(wffA.pred, argsB...)
		} else {
			wffB = wffA.DeepCopy()
		}
	case Unary:
		subL = replaceAllArgs(wffA.subL, argA, argB)

		wffB = NewUnaryWff(wffA.mop, subL)
	case Binary:
		subL, subR = replaceAllArgs(wffA.subL, argA, argB), replaceAllArgs(wffA.subR, argA, argB)

		wffB = NewBinaryWff(wffA.mop, subL, subR)
	case Quantified:
		if wffA.av == argA {
			wffB = wffA.DeepCopy()
		} else {
			subL = replaceAllArgs(wffA.subL, argA, argB)

			wffB = NewQuantifiedWff(wffA.mop, subL, wffA.pv, wffA.av)
		}
	}

	return
}

func replaceSomePreds(wffA *Wff, predA, predB Predicate, skip ...Symbol) (wffsB []*Wff) {
	var (
		wffB, subL, subR *Wff
		subsL, subsR     []*Wff
	)

	if slices.Contains(skip, wffA.mop) {
		wffsB = []*Wff{wffA.DeepCopy()}
	} else {
		switch wffA.kind {
		case Atomic:
			if wffA.pred == predA {
				wffB = NewAtomicWff(predB, wffA.args...)

				wffsB = []*Wff{wffA.DeepCopy(), wffB}
			} else {
				wffsB = []*Wff{wffA.DeepCopy()}
			}
		case Unary:
			subsL = replaceSomePreds(wffA.subL, predA, predB, skip...)

			for _, subL = range subsL {
				wffB = NewUnaryWff(wffA.mop, subL)

				wffsB = append(wffsB, wffB)
			}
		case Binary:
			subsL, subsR = replaceSomePreds(wffA.subL, predA, predB, skip...), replaceSomePreds(wffA.subR, predA, predB, skip...)

			for _, subL = range subsL {
				for _, subR = range subsR {
					wffB = NewBinaryWff(wffA.mop, subL, subR)

					wffsB = append(wffsB, wffB)
				}
			}
		case Quantified:
			if wffA.pv == predA {
				wffsB = []*Wff{wffA.DeepCopy()}
			} else {
				subsL = replaceSomePreds(wffA.subL, predA, predB, skip...)

				for _, subL = range subsL {
					wffB = NewQuantifiedWff(wffA.mop, subL, wffA.pv, wffA.av)

					wffsB = append(wffsB, wffB)
				}
			}
		}
	}

	return
}

func argCombos(args []Argument, argA, argB Argument) (combos [][]Argument) {
	var (
		arg               Argument
		next              [][]Argument
		combo, oldC, newC []Argument
	)

	combos = [][]Argument{{}}

	for _, arg = range args {
		next = [][]Argument{}

		for _, combo = range combos {
			if arg == argA {
				oldC, newC = slices.Clone(combo), slices.Clone(combo)
				oldC, newC = append(oldC, argB), append(newC, argA)

				next = append(next, oldC, newC)
			} else {
				oldC = slices.Clone(combo)

				oldC = append(oldC, arg)

				next = append(next, oldC)
			}
		}

		combos = next
	}

	return
}

func replaceSomeArgs(wffA *Wff, argA, argB Argument, skip ...Symbol) (wffsB []*Wff) {
	var (
		wffB, subL, subR *Wff
		subsL, subsR     []*Wff
		combos           [][]Argument
		combo            []Argument
	)

	if slices.Contains(skip, wffA.mop) {
		wffsB = []*Wff{wffA.DeepCopy()}
	} else {
		switch wffA.kind {
		case Atomic:
			if slices.Contains(wffA.args, argA) {
				combos = argCombos(wffA.args, argA, argB)

				for _, combo = range combos {
					wffB = NewAtomicWff(wffA.pred, combo...)

					wffsB = append(wffsB, wffB)
				}
			} else {
				wffsB = []*Wff{wffA.DeepCopy()}
			}
		case Unary:
			subsL = replaceSomeArgs(wffA.subL, argA, argB, skip...)

			for _, subL = range subsL {
				wffB = NewUnaryWff(wffA.mop, subL)

				wffsB = append(wffsB, wffB)
			}
		case Binary:
			subsL, subsR = replaceSomeArgs(wffA.subL, argA, argB, skip...), replaceSomeArgs(wffA.subR, argA, argB, skip...)

			for _, subL = range subsL {
				for _, subR = range subsR {
					wffB = NewBinaryWff(wffA.mop, subL, subR)

					wffsB = append(wffsB, wffB)
				}
			}
		case Quantified:
			if wffA.av == argA {
				wffsB = []*Wff{wffA.DeepCopy()}
			} else {
				subsL = replaceSomeArgs(wffA.subL, argA, argB, skip...)

				for _, subL = range subsL {
					wffB = NewQuantifiedWff(wffA.mop, subL, wffA.pv, wffA.av)

					wffsB = append(wffsB, wffB)
				}
			}
		}
	}

	return
}

func replaceSomeWffs(wffA *Wff, wffB, wffC *Wff, skip ...Symbol) (wffsD []*Wff) {
	var (
		wffD         *Wff
		subsL, subsR []*Wff
		subL, subR   *Wff
	)

	if slices.Contains(skip, wffA.mop) {
		wffsD = []*Wff{wffA.DeepCopy()}
	} else if wffA.Is(wffB) {
		wffsD = []*Wff{wffA.DeepCopy(), wffC.DeepCopy()}
	} else if !(wffB.Depth() < wffA.Depth()) {
		wffsD = []*Wff{wffA.DeepCopy()}
	} else {
		switch wffA.kind {
		// case Atomic: Don't check Atomic kind. The depth check handles it.
		case Unary:
			subsL = replaceSomeWffs(wffA.subL, wffB, wffC, skip...)

			for _, subL = range subsL {
				wffD = NewUnaryWff(wffA.mop, subL)

				wffsD = append(wffsD, wffD)
			}
		case Binary:
			subsL, subsR = replaceSomeWffs(wffA.subL, wffB, wffC, skip...), replaceSomeWffs(wffA.subR, wffB, wffC, skip...)

			for _, subL = range subsL {
				for _, subR = range subsR {
					wffD = NewBinaryWff(wffA.mop, subL, subR)

					wffsD = append(wffsD, wffD)
				}
			}
		case Quantified:
			subsL = replaceSomeWffs(wffA.subL, wffB, wffC, skip...)

			for _, subL = range subsL {
				wffD = NewQuantifiedWff(wffA.mop, subL, wffA.pv, wffA.av)

				wffsD = append(wffsD, wffD)
			}
		}
	}

	return
}

type AtomicPart interface {
	Predicate | Argument
}

func (wffA *Wff) Instantiate[AP AtomicPart](c AP) (wffB *Wff) {
	var (
		pc Predicate
		ac Argument
	)

	if wffA == nil {
		panic("Missing formula.")
	}

	if wffA.kind != Quantified {
		panic("The formula is not quantified.")
	}

	switch valC := any(c).(type) {
	case Predicate:
		if pc = valC; !slices.Contains(PredConsts, pc) {
			panic("Invalid predicate constant.")
		}
	case Argument:
		if ac = valC; !slices.Contains(ArgConsts, ac) {
			panic("Invalid argument constant.")
		}
	}

	if wffA.pv != NoPred && pc == NoPred {
		panic("Missing predicate constant for predicate variable.")
	}

	if wffA.av != NoArg && ac == NoArg {
		panic("Missing argument constant for argument variable.")
	}

	if wffA.pv != NoPred {
		wffB = replaceAllPreds(wffA.subL, wffA.pv, pc)
	} else if wffA.av != NoArg {
		wffB = replaceAllArgs(wffA.subL, wffA.av, ac)
	}

	return
}

func (wffA *Wff) Generalize[A AtomicPart](c, v A, mop Symbol) (wffsB map[WffHash]*Wff) {
	var (
		pc, pv Predicate
		ac, av Argument
		reps   []*Wff
		wffB   *Wff
	)

	if wffA == nil {
		panic("Missing formula.")
	}

	if mop != Exists && mop != ForAll {
		panic("Invalid operator for generalization.")
	}

	switch valC := any(c).(type) {
	case Predicate:
		if pc = valC; !slices.Contains(PredConsts, pc) {
			panic("Invalid predicate constant.")
		}
	case Argument:
		if ac = valC; !slices.Contains(ArgConsts, ac) {
			panic("Invalid argument constant.")
		}
	}

	switch valV := any(v).(type) {
	case Predicate:
		if pv = valV; !slices.Contains(PredVars, pv) {
			panic("Invalid predicate variable.")
		}
	case Argument:
		if av = valV; !slices.Contains(ArgVars, av) {
			panic("Invalid argument variable.")
		}
	}

	wffsB = map[WffHash]*Wff{}

	switch mop {
	case ForAll:
		if pc != NoPred && pv != NoPred {
			wffB = replaceAllPreds(wffA, pc, pv)
			wffB = NewQuantifiedWff(mop, wffB, pv, NoArg)

			wffsB[wffB.hash] = wffB
		} else if ac != NoArg && av != NoArg {
			wffB = replaceAllArgs(wffA, ac, av)
			wffB = NewQuantifiedWff(mop, wffB, NoPred, av)

			wffsB[wffB.hash] = wffB
		}
	case Exists:
		if pc != NoPred && pv != NoPred {

			reps = replaceSomePreds(wffA, pc, pv)

			for _, wffB = range reps {
				wffB = NewQuantifiedWff(mop, wffB, pv, NoArg)

				wffsB[wffB.hash] = wffB
			}
		} else if ac != NoArg && av != NoArg {
			reps = replaceSomeArgs(wffA, ac, av)

			for _, wffB = range reps {
				wffB = NewQuantifiedWff(mop, wffB, NoPred, av)

				wffsB[wffB.hash] = wffB
			}
		}
	}

	return
}

type ReplacePart interface {
	*Wff | Predicate | Argument
}

func (wffA *Wff) Replace[RP ReplacePart](thisA RP, thisB RP, skip ...Symbol) (wffsB map[WffHash]*Wff) {
	var (
		predA, predB Predicate
		argA, argB   Argument
		wffB, wffC   *Wff
		reps         []*Wff
	)

	if wffA == nil {
		panic("Missing formula.")
	}

	switch valA := any(thisA).(type) {
	case *Wff:
		wffB = valA
	case Predicate:
		if predA = valA; !slices.Contains(Preds, predA) {
			panic("Invalid predicate constant.")
		}
	case Argument:
		if argA = valA; !slices.Contains(Args, argA) {
			panic("Invalid argument constant.")
		}
	}

	switch valB := any(thisB).(type) {
	case *Wff:
		wffC = valB
	case Predicate:
		if predB = valB; !slices.Contains(Preds, predB) {
			panic("Invalid predicate constant.")
		}
	case Argument:
		if argB = valB; !slices.Contains(Args, argB) {
			panic("Invalid argument constant.")
		}
	}

	wffsB = map[WffHash]*Wff{}

	if predA != NoPred && predB != NoPred {
		reps = replaceSomePreds(wffA, predA, predB, skip...)

		for _, wffB = range reps {
			wffsB[wffB.hash] = wffB
		}
	} else if argA != NoArg && argB != NoArg {
		reps = replaceSomeArgs(wffA, argA, argB, skip...)

		for _, wffB = range reps {
			wffsB[wffB.hash] = wffB
		}
	} else if wffB != nil && wffC != nil {
		reps = replaceSomeWffs(wffA, wffB, wffC, skip...)

		for _, wffB = range reps {
			wffsB[wffB.hash] = wffB
		}
	}

	return
}
