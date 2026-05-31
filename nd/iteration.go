package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
	"iter"
)

type lineInfo struct {
	prf  *pr.Proof
	ln   *pr.Line
	wff  *fmla.Wff
	rule pr.NDRule
}

func newLineInfo(ln *pr.Line) (li *lineInfo) {
	li = &lineInfo{
		prf:  ln.GetProof(),
		ln:   ln,
		wff:  ln.GetWff(),
		rule: ln.GetRule(),
	}

	return
}

func genProofPairs(prf *pr.Proof, d int) (prfPairs iter.Seq2[*pr.Proof, *pr.Proof]) {
	prfPairs = func(yield func(prfA, prfB *pr.Proof) (cont bool)) {
		var (
			prfs       []*pr.Proof
			prfA, prfB *pr.Proof
		)

		prfs = prf.GetInnerProofs(true)

	GENPROOFPAIRS_OUTER:
		for _, prfA = range prfs {
			if !prfA.IsOpen() {
				continue
			}

			if d == 0 {
				if !yield(prfA, prfA) {
					break GENPROOFPAIRS_OUTER
				}
			}

			for _, prfB = range prfs {
				if !prfB.IsOpen() {
					continue
				}

				if !prfA.IsOuter(prfB) {
					continue
				}

				if prfA.GetModalDistance(prfB) != d {
					continue
				}

				if !yield(prfA, prfB) {
					break GENPROOFPAIRS_OUTER
				}
			}
		}
	}

	return
}

func genLineInfoSeq(prf *pr.Proof) (liSeq iter.Seq[*lineInfo]) {
	liSeq = func(yield func(liA *lineInfo) (cont bool)) {
		var (
			prfs []*pr.Proof
			prfA *pr.Proof
			lns  []*pr.Line
			ln   *pr.Line
			liA  *lineInfo
			ok   bool
		)

		prfs = prf.GetAllProofs()

	GENLININFOSEQ_OUTER:
		for _, prfA = range prfs {
			if !prfA.IsOpen() {
				continue
			}

			if _, _, ok = prfA.IsReachable(prf); !ok {
				continue
			}

			lns = prfA.GetLines()

			for _, ln = range lns {
				liA = newLineInfo(ln)

				if !yield(liA) {
					break GENLININFOSEQ_OUTER
				}
			}
		}
	}

	return
}

// genLineInfoPairs generates pairs of lineInfo structs such that both lineInfo structs
// are in open proofs, the first lineInfo struct's proof can reach second lineInfo's proof,
// and the modal distance between the two proofs is equal to the given distance.
//
// Parameters:
// - prf: the proof from which to generate lineInfo pairs.
// - d: the required modal distance from the outer to inner pairs' proofs.
//
// Returns:
// - liPairs: an iter.Seq2[*lineInfo, *lineInfo] whose elements meet the above conditions.
func genLineInfoPairs(prf *pr.Proof, d int) (liPairs iter.Seq2[*lineInfo, *lineInfo]) {
	var (
		prfO *pr.Proof
	)

	if prfO = prf.GetOuterProof(); prfO == nil {
		liPairs = func(yield func(liA, liB *lineInfo) (cont bool)) {
			var (
				lns      []*pr.Line
				dex      int
				lnA, lnB *pr.Line
				liA, liB *lineInfo
			)

			lns = prf.FlattenProof()

		GENLINEINFOPAIRS_OUTER:
			for dex, lnA = range lns {
				for _, lnB = range lns[dex+1:] {
					if liA, liB = newLineInfo(lnA), newLineInfo(lnB); !liA.prf.IsOpen() {
						continue GENLINEINFOPAIRS_OUTER
					} else if !liB.prf.IsOpen() {
						continue
					}

					if liA.prf != liB.prf && !liA.prf.IsOuter(liB.prf) {
						continue GENLINEINFOPAIRS_OUTER
					}

					if liA.prf.GetModalDistance(liB.prf) != d {
						continue
					}

					if !yield(liA, liB) {
						break GENLINEINFOPAIRS_OUTER
					}
				}
			}
		}
	} else {
		liPairs = genLineInfoPairs(prfO, d)
	}

	return
}

func genInstantiations(wff *fmla.Wff) (insts iter.Seq[*fmla.Wff]) {
	insts = func(yield func(wffI *fmla.Wff) (cont bool)) {
		var (
			wffsToWffsI map[*fmla.Wff][]*fmla.Wff
			wffI        *fmla.Wff
			wffsI       []*fmla.Wff
		)

		if fmla.HasOp(wff, fmla.Exists) {
			// TODO: Potentially limit this based on proof constants.
			wffsToWffsI = fmla.GetAllInstantiations(wff, fmla.PredConsts, fmla.ArgConsts)

		GENINSTANTIATIONS_OUTER:
			for wff, wffsI = range wffsToWffsI {
				if fmla.GetWffMop(wff) != fmla.Exists {
					continue
				}

				for _, wffI = range wffsI {
					if !yield(wffI) {
						break GENINSTANTIATIONS_OUTER
					}
				}
			}
		}
	}

	return
}

func genProofWffPairs(prf *pr.Proof) (prfWffPairs iter.Seq2[*pr.Proof, *fmla.Wff]) {
	prfWffPairs = func(yield func(prfA *pr.Proof, wffA *fmla.Wff) (cont bool)) {
		var (
			prfs       []*pr.Proof
			prfA       *pr.Proof
			wffG, wffA *fmla.Wff
			insts      iter.Seq[*fmla.Wff]
			lns        []*pr.Line
			ln         *pr.Line
		)

		prfs = prf.GetAllProofs()

	GENPROOFWFFPAIRS_OUTER:
		for _, prfA = range prfs {
			if !prfA.IsOpen() {
				continue
			}

			wffG = prfA.GetWffG()

			if !yield(prfA, wffG) {
				break GENPROOFWFFPAIRS_OUTER
			}

			insts = genInstantiations(wffG)

			for wffA = range insts {
				if !yield(prfA, wffA) {
					break GENPROOFWFFPAIRS_OUTER
				}
			}

			lns = prfA.GetLines()

			for _, ln = range lns {
				wffA = ln.GetWff()

				if !yield(prfA, wffA) {
					break GENPROOFWFFPAIRS_OUTER
				}

				insts = genInstantiations(wffA)

				for wffA = range insts {
					if !yield(prfA, wffA) {
						break GENPROOFWFFPAIRS_OUTER
					}
				}
			}
		}
	}

	return
}
