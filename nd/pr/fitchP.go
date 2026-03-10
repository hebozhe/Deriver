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
		deps = getJustificationDependencies(li.Ln)

		prf.lns = slices.DeleteFunc(prf.lns, func(ln *Line) (nix bool) {
			nix = !deps[ln]

			return
		})

		prfsI = prf.GetInnerProofs(false)

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

func newJustificationString(li *LineInfo, lis []*LineInfo) (sJ string) {
	var (
		dexJ1, dexJ2, dexJ3 int
	)

	if sJ = ruleToText[li.Rule]; li.Rule == Assumption {
		sJ += ruleToText[li.Purp]
	}

	switch {
	case li.J3 != nil:
		dexJ1 = slices.IndexFunc(lis, func(liN *LineInfo) (has bool) { has = liN.Ln == li.J1; return }) + 1

		dexJ2 = slices.IndexFunc(lis, func(liN *LineInfo) (has bool) { has = liN.Ln == li.J2; return }) + 1

		dexJ3 = slices.IndexFunc(lis, func(liN *LineInfo) (has bool) { has = liN.Ln == li.J3; return }) + 1

		switch li.Rule {
		case ExistsElim, DiamondElim:
			sJ += fmt.Sprintf("(%d,%d-%d)", dexJ1, dexJ2, dexJ3)
		default:
			sJ += fmt.Sprintf("(%d,%d,%d)", dexJ1, dexJ2, dexJ3)
		}
	case li.J2 != nil:
		dexJ1 = slices.IndexFunc(lis, func(liN *LineInfo) (has bool) { has = liN.Ln == li.J1; return }) + 1

		dexJ2 = slices.IndexFunc(lis, func(liN *LineInfo) (has bool) { has = liN.Ln == li.J2; return }) + 1

		switch li.Rule {
		case ToIntro, NegIntro, ForAllIntro, BoxIntro:
			sJ += fmt.Sprintf("(%d-%d)", dexJ1, dexJ2)
		default:
			sJ += fmt.Sprintf("(%d,%d)", dexJ1, dexJ2)
		}
	case li.J1 != nil:
		dexJ1 = slices.IndexFunc(lis, func(liN *LineInfo) (has bool) { has = liN.Ln == li.J1; return }) + 1

		sJ += fmt.Sprintf("(%d)", dexJ1)
	}

	return
}

func (prf *Proof) ConvertToFitchString() (sF string) {
	var (
		lis   []*LineInfo
		dex   int
		li    *LineInfo
		row   [3]string
		depth int
		rows  [][3]string
	)

	lis = prf.FlattenProof()

	for dex, li = range lis {
		row = [3]string{}

		row[0] = fmt.Sprintf("%d. ", dex+1)

		depth = li.Prf.GetDepth()

		row[1] = strings.Repeat("| ", depth)
		row[1] += fmla.GetWffString(li.Wff)

		row[2] = newJustificationString(li, lis)

		rows = append(rows, row)
	}

	rows = equalizeCellWidths(rows)

	for _, row = range rows {
		sF += fmt.Sprintf("%s %s %s\n", row[0], row[1], row[2])
	}

	return
}
