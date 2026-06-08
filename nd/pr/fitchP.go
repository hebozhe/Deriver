package pr

import (
	"Deriver/fmla"
	"fmt"
	"slices"
	"strings"
	"unicode/utf8"
)

func NameLogic(infS InfStrength, synB SynBreadth, modS ModStrength) (name string) {
	switch infS {
	case Implicational:
		name += "T"
	case Positive:
		name += "P"
	case Minimal:
		name += "M"
	case Intuitionistic:
		name += "I"
	case Classical:
		name += "C"
	}

	switch {
	case synB%QL == 0:
		name += "QL"
	case synB%NL == 0:
		name += "NL"
	case synB%PL == 0:
		name += "PL"
	}

	if synB%I == 0 {
		name += "i"
	}

	if synB%ML == 0 {
		name += "+"

		if modS%ModalK == 0 {
			name += "K"
		}

		if modS%ModalD == 0 {
			name += "D"
		}

		if modS%ModalM == 0 {
			name += "M"
		}

		if modS%Modal4 == 0 {
			name += "4"
		}

		if modS%ModalB == 0 {
			name += "B"
		}
	}

	return
}

var ruleToText map[NDRule]string = map[NDRule]string{
	Solve:        "SL",
	Premise:      "PR",
	Assumption:   "AS",
	TopIntro:     fmt.Sprintf("%cI", fmla.Top),
	ToIntro:      fmt.Sprintf("%cI", fmla.To),
	ToElim:       fmt.Sprintf("%cE", fmla.To),
	Reiteration:  "RE",
	TopElim:      fmt.Sprintf("%cE", fmla.Top),
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
	BoxElimC:     fmt.Sprintf("%cE", fmla.Box),
	BoxElimW:     fmt.Sprintf("%cE", fmla.Box),
	DiamondElim:  fmt.Sprintf("%cE", fmla.Diamond),
	DiamondIntro: fmt.Sprintf("%cI", fmla.Diamond),
	ElimD:        fmt.Sprintf("%cED", fmla.Box),
	IntroM:       fmt.Sprintf("%cIM", fmla.Diamond),
	ElimM:        fmt.Sprintf("%cEM", fmla.Box),
	Intro4:       fmt.Sprintf("%cI4", fmla.Box),
	Elim4:        fmt.Sprintf("%cE4", fmla.Diamond),
	IntroB:       fmt.Sprintf("%cIB", fmla.Box),
	ElimB:        fmt.Sprintf("%cEB", fmla.Diamond),
}

func equalizeCellWidths(rows [][4]string) (rowsU [][4]string) {
	var (
		dex                                            int
		row                                            [4]string
		max0, max1, max2, max3, len0, len1, len2, len3 int
	)

	for _, row = range rows {
		max0 = max(max0, utf8.RuneCountInString(row[0]))

		max1 = max(max1, utf8.RuneCountInString(row[1]))

		max2 = max(max2, utf8.RuneCountInString(row[2]))

		max3 = max(max3, utf8.RuneCountInString(row[3]))
	}

	for dex = range rows {
		len0 = utf8.RuneCountInString(rows[dex][0])

		rows[dex][0] += strings.Repeat(" ", max0-len0)

		len1 = utf8.RuneCountInString(rows[dex][1])

		rows[dex][1] += strings.Repeat(" ", max1-len1)

		len2 = utf8.RuneCountInString(rows[dex][2])

		rows[dex][2] = strings.Repeat(" ", max2-len2) + rows[dex][2]

		len3 = utf8.RuneCountInString(rows[dex][3])

		rows[dex][3] += strings.Repeat(" ", max3-len3)
	}

	rowsU = rows

	return
}

func newJustificationString(ln *Line, lns []*Line) (sJ string) {
	var (
		dexJ1, dexJ2, dexJ3 int
	)

	if sJ = ruleToText[ln.rule]; ln.rule == Assumption {
		sJ += ruleToText[ln.prf.purp]
	}

	switch {
	case ln.j3 != nil:
		dexJ1 = slices.IndexFunc(lns, func(lnN *Line) (has bool) { has = lnN == ln.j1; return }) + 1

		dexJ2 = slices.IndexFunc(lns, func(lnN *Line) (has bool) { has = lnN == ln.j2; return }) + 1

		dexJ3 = slices.IndexFunc(lns, func(lnN *Line) (has bool) { has = lnN == ln.j3; return }) + 1

		switch ln.rule {
		case ExistsElim, DiamondElim:
			sJ += fmt.Sprintf("(%d,%d-%d)", dexJ1, dexJ2, dexJ3)
		default:
			sJ += fmt.Sprintf("(%d,%d,%d)", dexJ1, dexJ2, dexJ3)
		}
	case ln.j2 != nil:
		dexJ1 = slices.IndexFunc(lns, func(lnN *Line) (has bool) { has = lnN == ln.j1; return }) + 1

		dexJ2 = slices.IndexFunc(lns, func(lnN *Line) (has bool) { has = lnN == ln.j2; return }) + 1

		switch ln.rule {
		case ToIntro, NegIntro, ForAllIntro, BoxIntro:
			sJ += fmt.Sprintf("(%d-%d)", dexJ1, dexJ2)
		default:
			sJ += fmt.Sprintf("(%d,%d)", dexJ1, dexJ2)
		}
	case ln.j1 != nil:
		dexJ1 = slices.IndexFunc(lns, func(lnN *Line) (has bool) { has = lnN == ln.j1; return }) + 1

		sJ += fmt.Sprintf("(%d)", dexJ1)
	}

	return
}

func (prf *Proof) ConvertToFitchString() (sF string) {
	var (
		lns  []*Line
		dex  int
		ln   *Line
		row  [4]string
		d    int
		rows [][4]string
	)

	lns = prf.FlattenProof()

	for dex, ln = range lns {
		row = [4]string{}

		row[0] = fmt.Sprintf("%d. ", dex+1)

		d = ln.prf.GetProofDepth()

		row[1] = strings.Repeat("| ", d)
		row[1] += fmla.GetWffString(ln.wff)

		row[2] = newJustificationString(ln, lns)

		if ln.rule == Assumption || dex == 0 {
			row[3] = ": " + fmla.GetWffString(ln.prf.wffG)
		}

		rows = append(rows, row)
	}

	rows = equalizeCellWidths(rows)

	for _, row = range rows {
		sF += fmt.Sprintf("%s %s %s%s\n", row[0], row[1], row[2], row[3])
	}

	return
}
