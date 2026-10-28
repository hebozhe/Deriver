package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
	"slices"
)

func wffIs(wff *fmla.Wff) (keep func(ln *pr.Line) (ok bool)) {
	keep = func(ln *pr.Line) (ok bool) {
		ok = ln.Wff().Is(wff)

		return
	}

	return
}

func mopIs(mop fmla.Symbol) (keep func(ln *pr.Line) (ok bool)) {
	keep = func(ln *pr.Line) (ok bool) {
		ok = ln.Wff().Mop() == mop

		return
	}

	return
}

func predIs(pred fmla.Predicate) (keep func(ln *pr.Line) (ok bool)) {
	keep = func(ln *pr.Line) (ok bool) {
		ok = ln.Wff().Pred() == pred

		return
	}

	return
}

func subIs(loc string, wff *fmla.Wff) (keep func(ln *pr.Line) (ok bool)) {
	keep = func(ln *pr.Line) (ok bool) {
		var sub *fmla.Wff = ln.Wff().Locate(loc)

		ok = sub != nil && sub.Is(wff)

		return
	}

	return
}

func subMopIs(loc string, mop fmla.Symbol) (keep func(ln *pr.Line) (ok bool)) {
	keep = func(ln *pr.Line) (ok bool) {
		var sub *fmla.Wff = ln.Wff().Locate(loc)

		ok = sub != nil && sub.Mop() == mop

		return
	}

	return
}

func subPredIs(loc string, pred fmla.Predicate) (keep func(ln *pr.Line) (ok bool)) {
	keep = func(ln *pr.Line) (ok bool) {
		var sub *fmla.Wff = ln.Wff().Locate(loc)

		ok = sub != nil && sub.Pred() == pred

		return
	}

	return
}

func subsMmatch(locA, locB string) (keep func(ln *pr.Line) (ok bool)) {
	keep = func(ln *pr.Line) (ok bool) {
		var (
			wff, subA, subB *fmla.Wff
		)

		wff = ln.Wff()

		subA, subB = wff.Locate(locA), wff.Locate(locB)

		ok = subA != nil && subB != nil && subA.Is(subB)

		return
	}

	return
}

func wffHas[WP fmla.WffPart](part WP) (keep func(ln *pr.Line) (ok bool)) {
	keep = func(ln *pr.Line) (ok bool) {
		ok = ln.Wff().Has(part)

		return
	}

	return
}

func strIs(s string) (keep func(ln *pr.Line) (ok bool)) {
	keep = func(ln *pr.Line) (ok bool) {
		ok = ln.Wff().String() == s

		return
	}

	return
}

func ruleIs(rule pr.NDRule) (keep func(ln *pr.Line) (ok bool)) {
	keep = func(ln *pr.Line) (ok bool) {
		ok = ln.Rule() == rule

		return
	}

	return
}

func or(reqs ...func(ln *pr.Line) (ok bool)) (keep func(ln *pr.Line) (ok bool)) {
	keep = func(ln *pr.Line) (ok bool) {
		var (
			lenR int
			req  func(ln *pr.Line) (ok bool)
		)

		if lenR = len(reqs); 0 < lenR {
			for _, req = range reqs {
				if ok = req(ln); ok {
					break
				}
			}
		} else {
			ok = true
		}

		return
	}

	return
}

func nor(reqs ...func(ln *pr.Line) (ok bool)) (keep func(ln *pr.Line) (ok bool)) {
	keep = func(ln *pr.Line) (ok bool) {
		var (
			lenR int
			req  func(ln *pr.Line) (ok bool)
		)

		ok = true

		if lenR = len(reqs); 0 < lenR {
			for _, req = range reqs {
				if ok = !req(ln); !ok {
					break
				}
			}
		}

		return
	}

	return
}

func keepLines(prfA, prfB *pr.Prf, reqs ...func(*pr.Line) bool) (lns []*pr.Line) {
	switch {
	case prfA == nil && prfB == nil:
		lns = []*pr.Line{}
	case prfA == nil, prfA == prfB:
		lns = slices.Collect(prfB.Lines())
	case prfB == nil:
		lns = slices.Collect(prfA.Lines())
	default:
		lns = slices.AppendSeq(lns, prfA.Lines())
		lns = slices.AppendSeq(lns, prfB.Lines())
	}

	lns = slices.DeleteFunc(lns, func(ln *pr.Line) (nix bool) {
		var (
			req func(*pr.Line) bool
		)

		for _, req = range reqs {
			if nix = !req(ln); nix {
				break
			}
		}

		return
	})

	return
}
