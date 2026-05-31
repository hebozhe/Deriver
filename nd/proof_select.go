package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
	"cmp"
	"slices"
)

func deleteClosed(prfA *pr.Proof) (nix bool) {
	nix = !prfA.IsOpen()

	return
}

func deleteMissingWffG(wffG *fmla.Wff) (delFunc func(prf *pr.Proof) (nix bool)) {
	delFunc = func(prf *pr.Proof) (nix bool) {
		var (
			wff *fmla.Wff
		)

		wff = prf.GetWffG()

		nix = !fmla.IsIdentical(wff, wffG)

		return
	}

	return
}

func deleteMissingWffGMop(mop fmla.Symbol) (delFunc func(prf *pr.Proof) (nix bool)) {
	delFunc = func(prf *pr.Proof) (nix bool) {
		var wffG *fmla.Wff

		wffG = prf.GetWffG()

		nix = fmla.GetWffMop(wffG) != mop

		return
	}

	return
}

func innerToOuterSort(prfA, prfB *pr.Proof) (comp int) {
	var (
		pdA, pdB int
	)

	pdA, pdB = prfA.GetProofDepth(), prfB.GetProofDepth()

	comp = cmp.Compare(pdB, pdA)

	return
}

func outerToInnerSort(prfA, prfB *pr.Proof) (comp int) {
	var (
		pdA, pdB int
	)

	pdA, pdB = prfA.GetProofDepth(), prfB.GetProofDepth()

	comp = cmp.Compare(pdA, pdB)

	return
}

func getOpenInnerProofs(prf *pr.Proof, sort func(prfA, prfB *pr.Proof) (comp int)) (prfsI []*pr.Proof) {
	prfsI = prf.GetInnerProofsAtModalDistance(true, 0)
	prfsI = slices.DeleteFunc(prfsI, deleteClosed)
	slices.SortStableFunc(prfsI, sort)

	return
}
