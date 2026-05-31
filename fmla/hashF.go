package fmla

import (
	"hash"
	"hash/fnv"
)

type WffHash uint64

func hashWff(wff *Wff) (h WffHash) {
	if wff == nil {
		panic("Invalid WffTree")
	}

	var hash64 hash.Hash64 = fnv.New64a()

	hashWffInto(hash64, wff)

	h = WffHash(hash64.Sum64())

	return
}

func hashWffInto(hash64 hash.Hash64, wff *Wff) {
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
		hash64.Write([]byte{byte(wff.pv)})
		hash64.Write([]byte{byte(wff.av)})

		hashWffInto(hash64, wff.subL)
	default:
		panic("invalid WffKind")
	}
}

func GetWffHash(wff *Wff) (h WffHash) {
	h = hashWff(wff)

	return
}

func IsIdentical(wffA, wffB *Wff) (is bool) {
	is = wffA.h == wffB.h

	return
}

func IsIdenticalAtLocales(wff *Wff, locA, locB string) (is bool) {
	var (
		wffA, wffB *Wff
	)

	if wff == nil {
		panic("Invalid WffTree")
	}

	wffA, wffB = RetrieveSubformula(wff, locA), RetrieveSubformula(wff, locB)

	is = wffA.h == wffB.h

	return
}
