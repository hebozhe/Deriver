package pr

import (
	"Deriver/fmla"
	"fmt"
	"slices"
	"strings"
	"unicode/utf8"
)

var ruleToText map[NDRule]string = map[NDRule]string{
	Solve:        "SL",
	Premise:      "PR",
	Theorem:      "TH",
	Assumption:   "AS",
	TopIntro:     fmt.Sprintf("%cI", fmla.Top),
	ToIntro:      fmt.Sprintf("%cI", fmla.To),
	ToElim:       fmt.Sprintf("%cE", fmla.To),
	Reiteration:  "RE",
	WedgeIntro:   fmt.Sprintf("%cI", fmla.Wedge),
	WedgeElim:    fmt.Sprintf("%cE", fmla.Wedge),
	VeeIntro:     fmt.Sprintf("%cI", fmla.Vee),
	VeeElim:      fmt.Sprintf("%cE", fmla.Vee),
	IffIntro:     fmt.Sprintf("%cI", fmla.Iff),
	IffElim:      fmt.Sprintf("%cE", fmla.Iff),
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
	DiamondElim:  fmt.Sprintf("%cE", fmla.Diamond),
	DiamondIntro: fmt.Sprintf("%cI", fmla.Diamond),
	IntroK:       fmt.Sprintf("%cIK", fmla.Box),
	ElimD:        fmt.Sprintf("%cED", fmla.Box),
	IntroM:       fmt.Sprintf("%cIM", fmla.Diamond),
	ElimM:        fmt.Sprintf("%cEM", fmla.Box),
	Intro4:       fmt.Sprintf("%cI4", fmla.Box),
	Elim4:        fmt.Sprintf("%cE4", fmla.Diamond),
	IntroB:       fmt.Sprintf("%cIB", fmla.Box),
	ElimB:        fmt.Sprintf("%cEB", fmla.Diamond),
}

type FitchLine struct {
	wff *fmla.WffTree

	rule                      NDRule
	dexL, dexJ1, dexJ2, dexJ3 int
	prf                       *Proof
	pos                       []int
}

func (prf *Proof) FlattenProof() (lis []*LineInfo) {
	var (
		lenI int
		prfI *Proof
		lisI []*LineInfo
	)

	lis, _ = prf.GetLocalLines()

	if lenI = len(prf.prfsI); 0 < lenI {
		for _, prfI = range prf.prfsI {
			lisI = prfI.FlattenProof()

			lis = append(lis, lisI...)
		}
	}

	return
}

func renumberFitchLines(fls []*FitchLine) (flsU []*FitchLine) {
	var (
		renums map[int]int
		dex    int
		fl     *FitchLine
	)

	renums = map[int]int{}

	for dex, fl = range fls {
		renums[fl.dexL] = dex
	}

	for dex, fl = range fls {
		fls[dex].dexL = renums[fl.dexL]

		if -1 < fl.dexJ1 {
			fls[dex].dexJ1 = renums[fl.dexJ1]
		}

		if -1 < fl.dexJ2 {
			fls[dex].dexJ2 = renums[fl.dexJ2]
		}

		if -1 < fl.dexJ3 {
			fls[dex].dexJ3 = renums[fl.dexJ3]
		}
	}

	flsU = fls

	return
}

func sortFitchLines(fls []*FitchLine) (flsU []*FitchLine) {
	var (
		dexF, dexM, lenF int
		fl               *FitchLine
	)

	lenF = len(fls)

	for dexF = lenF - 1; -1 < dexF; dexF -= 1 {
		fl = fls[dexF]

		if dexM = max(fl.dexL, fl.dexJ1, fl.dexJ2, fl.dexJ3); dexM != dexF {
			fls = slices.Insert(fls, dexM+1, fls[dexF])

			fls = slices.Delete(fls, dexF, dexF+1)

			fls = renumberFitchLines(fls)

			dexF = dexM + 1
		}
	}

	flsU = fls

	return
}

func (prf *Proof) GetFitchLines() (fls []*FitchLine) {
	var (
		lis []*LineInfo
		dex int
		li  *LineInfo
		fl  *FitchLine
	)

	lis = prf.FlattenProof()

	for dex, li = range lis {
		fl = &FitchLine{
			wff: li.Ln.wff,

			rule: li.Rule,
			dexL: dex,
			dexJ1: slices.IndexFunc(lis, func(liN *LineInfo) (has bool) {
				has = liN.Ln == li.J1

				return
			}),
			dexJ2: slices.IndexFunc(lis, func(liN *LineInfo) (has bool) {
				has = liN.Ln == li.J2

				return
			}),
			dexJ3: slices.IndexFunc(lis, func(liN *LineInfo) (has bool) {
				has = liN.Ln == li.J3

				return
			}),
			prf: li.Prf,
			pos: li.Prf.GetPosition(),
		}

		fls = append(fls, fl)
	}

	fls = sortFitchLines(fls)

	return
}

func (prf *Proof) MinimizeProof() (prfU *Proof) {
	var (
		li    *LineInfo
		met   bool
		deps  map[*Line]bool
		prfsI []*Proof
		prfI  *Proof
	)

	if prf.prfO != nil {
		prf.prfO = prf.prfO.MinimizeProof()
	} else if li, met = prf.IsWffGMet(); met {
		deps = getJustDeps(li.Ln)

		prf.lns = slices.DeleteFunc(prf.lns, func(ln *Line) (nix bool) {
			nix = !deps[ln]

			return
		})

		prfsI = prf.GetInnerProofs()

		for _, prfI = range prfsI {
			prfI.lns = slices.DeleteFunc(prfI.lns, func(ln *Line) (nix bool) {
				nix = !deps[ln]

				return
			})
		}
	}

	return
}

func equalizeCellWidths(rows [][3]string) (rowsU [][3]string) {
	var (
		dex                                int
		row                                [3]string
		max0, max1, max2, len0, len1, len2 int
	)

	for _, row = range rows {
		max0 = max(max0, utf8.RuneCountInString(row[0]))

		max1 = max(max1, utf8.RuneCountInString(row[1]))

		max2 = max(max2, utf8.RuneCountInString(row[2]))
	}

	for dex = range rows {
		len0 = utf8.RuneCountInString(rows[dex][0])

		rows[dex][0] += strings.Repeat(" ", max0-len0)

		len1 = utf8.RuneCountInString(rows[dex][1])

		rows[dex][1] += strings.Repeat(" ", max1-len1)

		len2 = utf8.RuneCountInString(rows[dex][2])

		rows[dex][2] = strings.Repeat(" ", max2-len2) + rows[dex][2]
	}

	rowsU = rows

	return
}

func newJustificationString(fl *FitchLine) (sJ string) {
	if sJ = ruleToText[fl.rule]; fl.rule == Assumption {
		sJ += ruleToText[fl.prf.purp]
	}

	switch {
	case -1 < fl.dexJ3:
		sJ += fmt.Sprintf("(%d,%d,%d)", fl.dexJ1, fl.dexJ2, fl.dexJ3)
	case -1 < fl.dexJ2:
		sJ += fmt.Sprintf("(%d,%d)", fl.dexJ1, fl.dexJ2)
	case -1 < fl.dexJ1:
		sJ += fmt.Sprintf("(%d)", fl.dexJ1)
	}

	return
}

func (prf *Proof) ConvertToFitchString() (sF string) {
	var (
		fls   []*FitchLine
		fl    *FitchLine
		row   [3]string
		depth int
		rows  [][3]string
	)

	fls = prf.GetFitchLines()

	for _, fl = range fls {
		row = [3]string{}

		row[0] = fmt.Sprintf("%d. ", fl.dexL)

		depth = len(fl.pos)

		row[1] = strings.Repeat("| ", depth)
		row[1] += fmla.GetWffString(fl.wff)

		row[2] = newJustificationString(fl)

		rows = append(rows, row)
	}

	rows = equalizeCellWidths(rows)

	for _, row = range rows {
		sF += fmt.Sprintf("%s %s %s\n", row[0], row[1], row[2])
	}

	return
}
