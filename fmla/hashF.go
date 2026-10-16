package fmla

import (
	"encoding/binary"
	"hash"
	"hash/fnv"
)

type WffHash uint64

func hashWff(wff *Wff) (h WffHash) {
	var (
		hash64 hash.Hash64
		buf    [8]byte
		arg    Argument
	)

	hash64 = fnv.New64a()

	// wff.kind must remain a small enum for direct byte caching.
	hash64.Write([]byte{byte(wff.kind)})

	switch wff.kind {
	case Atomic:
		hash64.Write([]byte(string(wff.pred)))

		for _, arg = range wff.args {
			hash64.Write([]byte(string(arg)))
		}
	case Unary:
		hash64.Write([]byte(string(wff.mop)))

		binary.BigEndian.PutUint64(buf[:], uint64(wff.subL.hash))
		hash64.Write(buf[:])
	case Binary:
		hash64.Write([]byte(string(wff.mop)))

		binary.BigEndian.PutUint64(buf[:], uint64(wff.subL.hash))
		hash64.Write(buf[:])

		binary.BigEndian.PutUint64(buf[:], uint64(wff.subR.hash))
		hash64.Write(buf[:])
	case Quantified:
		hash64.Write([]byte(string(wff.mop)))
		hash64.Write([]byte(string(wff.pv)))
		hash64.Write([]byte(string(wff.av)))

		binary.BigEndian.PutUint64(buf[:], uint64(wff.subL.hash))
		hash64.Write(buf[:])
	}

	h = WffHash(hash64.Sum64())

	return
}
