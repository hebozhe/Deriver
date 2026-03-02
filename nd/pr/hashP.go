package pr

import (
	"Deriver/fmla"
	"fmt"
)

type LineHash string

func (prf *Proof) hashLine(ln *Line) (lh LineHash) {
	var s string

	s = fmt.Sprintf("[%s]⊦{%s}%s: %s",
		fmla.GetWffString(prf.lns[0].wff),
		ruleToText[prf.purp],
		fmla.GetWffString(prf.wffG),
		fmla.GetWffString(ln.wff),
	)

	lh = LineHash(s)

	return
}
