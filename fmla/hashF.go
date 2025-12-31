package fmla

import (
	"hash"
	"hash/fnv"
)

func hashWff(wff *WffTree) (h uint64) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	var hash64 hash.Hash64 = fnv.New64a()

	hashWffInto(hash64, wff)

	h = hash64.Sum64()

	return
}

func hashWffInto(hash64 hash.Hash64, wff *WffTree) {
	// Node kind tag
	hash64.Write([]byte{byte(wff.kind)})

	switch wff.kind {

	case Atomic:
		hash64.Write([]byte{byte(wff.pred)})
		hash64.Write([]byte(wff.args))

	case Unary:
		hash64.Write([]byte{byte(wff.mop)})

		hashWffInto(hash64, wff.subL)
	case Binary:
		hash64.Write([]byte{byte(wff.mop)})

		hashWffInto(hash64, wff.subL)
		hashWffInto(hash64, wff.subR)
	case Quantified:
		hash64.Write([]byte{byte(wff.mop)})
		hash64.Write([]byte{byte(wff.pVar)})
		hash64.Write([]byte{byte(wff.aVar)})

		hashWffInto(hash64, wff.subL)
	default:
		panic("invalid WffKind")
	}
}
