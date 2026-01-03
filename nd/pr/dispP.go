package pr

import (
	"Deriver/fmla"
	"cmp"
	"fmt"
	"slices"
	"strings"
	"unicode/utf8"
)

type FitchLine struct {
	ln    *Line  // The line to be displayed.
	pid   []uint // The identifier for the status of the inner proof.
	depth uint   // The depth in the fitch proof, as inferred from the pid length.
	LnNum uint   // The line number in the fitch proof.
	Fmla  string // The formula, represented as a string.
	Just  string // The rule and other lines justifying the formula.
	Purp  string // The purpose of the line, if Just is Assumption.
}

var ndRuleToName map[NDRule]string = map[NDRule]string{
	Assumption:   "SM",
	Premise:      "PR",
	Theorem:      "TH",
	TopIntro:     fmt.Sprintf("%cI", fmla.Top),
	ToIntro:      fmt.Sprintf("%cI", fmla.To),
	ToElim:       fmt.Sprintf("%cE", fmla.To),
	WedgeIntro:   fmt.Sprintf("%cI", fmla.Wedge),
	WedgeElim:    fmt.Sprintf("%cE", fmla.Wedge),
	VeeIntro:     fmt.Sprintf("%cI", fmla.Vee),
	VeeElim:      fmt.Sprintf("%cE", fmla.Vee),
	IffIntro:     fmt.Sprintf("%cI", fmla.Iff),
	IffElim:      fmt.Sprintf("%cE", fmla.Iff),
	Reit:         "Re.",
	BotIntro:     fmt.Sprintf("%cI", fmla.Bot),
	BotElim:      fmt.Sprintf("%cE", fmla.Bot),
	NegIntro:     fmt.Sprintf("%cI", fmla.Neg),
	NegElim:      fmt.Sprintf("%cE", fmla.Neg),
	ForAllIntro:  fmt.Sprintf("%cI", fmla.ForAll),
	ForAllElim:   fmt.Sprintf("%cE", fmla.ForAll),
	ExistsIntro:  fmt.Sprintf("%cI", fmla.Exists),
	ExistsElim:   fmt.Sprintf("%cE", fmla.Exists),
	EqualsIntro:  fmt.Sprintf("%cI", fmla.Equals),
	EqualsElim:   fmt.Sprintf("%cE", fmla.Equals),
	BoxIntro:     fmt.Sprintf("%cI", fmla.Box),
	BoxElim:      fmt.Sprintf("%cE", fmla.Box),
	DiamondIntro: fmt.Sprintf("%cI", fmla.Diamond),
	DiamondElim:  fmt.Sprintf("%cE", fmla.Diamond),
	IntroD:       "DI",
	IntroM:       "MI",
	ElimM:        "ME",
	Intro4:       "4I",
	Elim4:        "4E",
	IntroB:       "BI",
	ElimB:        "BE",
}

func flattenProofToFitchLines(prf *Proof, lnsM map[*Line]struct{}) (fls []*FitchLine) {
	var (
		dex  int
		ln   *Line
		ok   bool
		prfI *Proof
		fl   *FitchLine
		flsI []*FitchLine
	)

	for dex, ln = range prf.lns {
		if _, ok = lnsM[ln]; !ok {
			continue
		}

		fl = &FitchLine{
			ln:    prf.lns[dex],
			pid:   append([]uint{}, prf.pid...),
			LnNum: 0, // This will be filled in later.
			Fmla:  fmla.GetWffString(ln.wff),
			Just:  ndRuleToName[ln.rule],
			Purp:  ndRuleToName[prf.purp],
		}

		fls = append(fls, fl)

		delete(lnsM, ln)
	}

	for _, prfI = range prf.inner {
		flsI = flattenProofToFitchLines(prfI, lnsM)

		fls = append(fls, flsI...)
	}

	return
}

func separateFreeAndBoundFitchLines(fls []*FitchLine) (flsF []*FitchLine, flsB []*FitchLine) {
	var (
		fl *FitchLine
	)

	for _, fl = range fls {
		if fl.ln.rule == Assumption || fl.ln.j1 == nil {
			flsF = append(flsF, fl)
		} else {
			flsB = append(flsB, fl)
		}
	}

	// Sort the free fitch lines first by pid, and then by dex.
	slices.SortStableFunc(flsF, func(flA, flB *FitchLine) (comp int) {
		var (
			lenA, lenB, dex int
		)

		lenA, lenB = len(flA.pid), len(flB.pid)

		switch {
		case lenA < lenB:
			for dex = 0; dex < lenA; dex += 1 {
				if comp = cmp.Compare(flA.pid[dex], flB.pid[dex]); comp != 0 {
					break
				}

				comp = -1
			}
		case lenA == lenB:
			for dex = 0; dex < lenA; dex += 1 {
				if comp = cmp.Compare(flA.pid[dex], flB.pid[dex]); comp != 0 {
					break
				}
			}
		case lenB < lenA:
			for dex = 0; dex < lenB; dex += 1 {
				if comp = cmp.Compare(flA.pid[dex], flB.pid[dex]); comp != 0 {
					break
				}

				comp = 1
			}
		}

		// If the proof IDs are equal, compare their line indices.
		if comp == 0 {
			comp = cmp.Compare(flA.ln.dex, flB.ln.dex)
		}

		return
	})

	return
}

func okToInsert(flN *FitchLine, fls []*FitchLine) (dexI int, ok bool) {
	var (
		dexP, dexJ1, dexJ2, dexJ3 int
		findDexJ                  func(tgt *Line) (dexJ int)
	)

	// dexP ensures that the Fitch line is never inserted
	// before the first Fitch line with the same proof ID,
	// which matters for all scopes, but particularly for rules like Reit.
	dexP = slices.IndexFunc(fls, func(fl *FitchLine) (has bool) {
		has = slices.Equal(fl.pid, flN.pid) && fl.ln.rule == Assumption

		return
	})

	findDexJ = func(jln *Line) (dexJ int) {
		dexJ = slices.IndexFunc(fls, func(fl *FitchLine) (has bool) {
			has = fl.ln == jln

			return
		})

		return
	}

	if flN.ln.j1 != nil {
		dexJ1 = findDexJ(flN.ln.j1)
	}

	if flN.ln.j2 != nil {
		dexJ2 = findDexJ(flN.ln.j2)
	}

	if flN.ln.j3 != nil {
		dexJ3 = findDexJ(flN.ln.j3)
	}

	if ok = dexJ1 != -1 && dexJ2 != -1 && dexJ3 != -1; ok {
		// Add 1 to the maximum dex.
		dexI = max(dexP, dexJ1, dexJ2, dexJ3) + 1
	} else {
		dexI = -1
	}

	return
}

func reinsertBoundFitchLines(flsF []*FitchLine, flsB []*FitchLine) (fls []*FitchLine) {
	var (
		lenB, dexI, cyc int
		fl              *FitchLine
		ok              bool
	)

	fls = append(fls, flsF...)

	lenB = len(flsB)

	for 0 < lenB {
		fl, flsB = flsB[0], flsB[1:]

		if dexI, ok = okToInsert(fl, fls); ok {
			fls = slices.Insert(fls, dexI, fl)

			lenB, cyc = lenB-1, 0
		} else {
			flsB = append(flsB, fl)

			cyc += 1

			if cyc == lenB {
				panic("Infinite loop: Needed justification lines are missing.")
			}
		}
	}

	return
}

func formatJustField(flN *FitchLine, fls []*FitchLine) (js string) {
	var (
		jln1, jln2, jln3 uint
		fl               *FitchLine
		findJLn          func(ln *Line, fls []*FitchLine) (jln uint)
	)

	js = ndRuleToName[flN.ln.rule]

	findJLn = func(ln *Line, fls []*FitchLine) (jln uint) {
		for _, fl = range fls {
			if fl.ln == ln {
				jln = fl.LnNum

				break
			}
		}

		return
	}

	switch {
	case flN.ln.j1 == nil:
		// Do nothing, since this means j2 and j3 are nil.
	case flN.ln.j2 == nil:
		jln1 = findJLn(flN.ln.j1, fls)

		js += fmt.Sprintf(" (%d)", jln1)
	case flN.ln.j3 == nil:
		jln1 = findJLn(flN.ln.j1, fls)
		jln2 = findJLn(flN.ln.j2, fls)

		js += fmt.Sprintf(" (%d, %d)", jln1, jln2)
	default:
		jln1 = findJLn(flN.ln.j1, fls)
		jln2 = findJLn(flN.ln.j2, fls)
		jln3 = findJLn(flN.ln.j3, fls)

		js += fmt.Sprintf(" (%d, %d, %d)", jln1, jln2, jln3)
	}

	return
}

func NewFitchLines(prf *Proof) (fls []*FitchLine, met bool) {
	var (
		lnG  *Line
		lnsM map[*Line]struct{}
		flsB []*FitchLine
		dex  int
	)

	if _, lnG, met = prf.HeadGoalMet(); met {
		lnsM = markUsedLines(lnG)

		fls = flattenProofToFitchLines(prf, lnsM)

		fls, flsB = separateFreeAndBoundFitchLines(fls)

		fls = reinsertBoundFitchLines(fls, flsB)

		for dex = range fls {
			fls[dex].LnNum = uint(dex + 1)
		}

		for dex = range fls {
			fls[dex].Just = formatJustField(fls[dex], fls)
		}
	}

	return
}

func prettifyFitchLineStrings(ss []string) (ssP []string) {
	var (
		lenS, dexA, dexB, nA, nB int
		gap                      string
	)

	lenS = len(ss)

	for dexA = 0; dexA < lenS; dexA += 1 {
		for dexB = dexA + 1; dexB < lenS; dexB += 1 {
			nA = utf8.RuneCountInString(ss[dexA])

			nB = utf8.RuneCountInString(ss[dexB])

			switch {
			case nA < nB:
				gap = strings.Repeat(" ", nB-nA)

				ss[dexA] = strings.Replace(ss[dexA], " by ", gap+" by ", 1)
			case nB < nA:
				gap = strings.Repeat(" ", nA-nB)

				ss[dexB] = strings.Replace(ss[dexB], " by ", gap+" by ", 1)
			}
		}
	}

	ssP = append(ssP, ss...)

	return
}

func NewFitchLineString(prf *Proof) (s string, met bool) {
	var (
		fls []*FitchLine
		fl  *FitchLine
		ss  []string
	)

	fls, met = NewFitchLines(prf)

	for _, fl = range fls {
		s = fmt.Sprintf("%4d.", fl.LnNum)
		s += strings.Repeat("|", int(fl.depth))
		s += " " + fl.Fmla
		s += " by " + fl.Just + fl.Purp

		ss = append(ss, s)
	}

	ss = prettifyFitchLineStrings(ss)

	s = strings.Join(ss, "\n")

	return
}
