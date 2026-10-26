package pr

import (
	"Deriver/fmla"
	"fmt"
	"slices"
	"strings"
	"unicode/utf8"
)

var ruleToString map[NDRule]string = map[NDRule]string{
	Solve:    "",
	Prem:     "Prem",
	Ass:      "Ass",
	TopI:     fmt.Sprintf("%cI", fmla.Top),
	ToI:      fmt.Sprintf("%cI", fmla.To),
	ToE:      fmt.Sprintf("%cE", fmla.To),
	Reit:     "Reit",
	Thm:      "Thm",
	WedgeI:   fmt.Sprintf("%cI", fmla.Wedge),
	WedgeE:   fmt.Sprintf("%cE", fmla.Wedge),
	VeeI:     fmt.Sprintf("%cI", fmla.Vee),
	VeeE:     fmt.Sprintf("%cE", fmla.Vee),
	IffI:     fmt.Sprintf("%cI", fmla.Iff),
	IffE:     fmt.Sprintf("%cE", fmla.Iff),
	BotI:     fmt.Sprintf("%cI", fmla.Bot),
	BotE:     fmt.Sprintf("%cE", fmla.Bot),
	NegI:     fmt.Sprintf("%cI", fmla.Neg),
	NegE:     fmt.Sprintf("%cE", fmla.Neg),
	Jan:      "Jan",
	Göd:      "Göd",
	Sme:      "Sme",
	EqualI:   fmt.Sprintf("%cI", fmla.Equal),
	EqualE:   fmt.Sprintf("%cE", fmla.Equal),
	ForAllI:  fmt.Sprintf("%cI", fmla.ForAll),
	ForAllE:  fmt.Sprintf("%cE", fmla.ForAll),
	ExistsI:  fmt.Sprintf("%cI", fmla.Exists),
	ExistsE:  fmt.Sprintf("%cE", fmla.Exists),
	BoxCon:   fmt.Sprintf("%cCon", fmla.Box),
	DmdCon:   fmt.Sprintf("%cCon", fmla.Dmd),
	BoxIntEw: fmt.Sprintf("%cInt[Ew]", fmla.Box),
	DmdIntEw: fmt.Sprintf("%cInt[Ew]", fmla.Dmd),
	BoxIntEn: fmt.Sprintf("%cInt[En]", fmla.Box),
	DmdIntEn: fmt.Sprintf("%cInt[En]", fmla.Dmd),
	BoxIntEs: fmt.Sprintf("%cInt[Es]", fmla.Box),
	DmdIntEs: fmt.Sprintf("%cInt[Es]", fmla.Dmd),
	DmdI:     fmt.Sprintf("%cI", fmla.Dmd),
	BoxMon:   fmt.Sprintf("%cMon", fmla.Box),
	DmdMon:   fmt.Sprintf("%cMon", fmla.Dmd),
	BoxE:     fmt.Sprintf("%cE", fmla.Box),
	DmdE:     fmt.Sprintf("%cE", fmla.Dmd),
	BoxI:     fmt.Sprintf("%cI", fmla.Box),
	NegDmdI:  fmt.Sprintf("%c%cI", fmla.Neg, fmla.Dmd),
	BoxAgg:   fmt.Sprintf("%cAgg", fmla.Box),
	ReitC:    "Reit[C]",
	ReitK:    "Reit[K]",
	RuleD:    "D",
	IntroT:   "TI",
	ElimT:    "TE",
	Intro4:   "4I",
	Elim4:    "4E",
	IntroB:   "BI",
	ElimB:    "BE",
	Intro5:   "5I",
	Elim5:    "5E",
}

func equalizeCellWidths(rows [][4]string) (rowsE [][4]string) {
	var (
		lenR, dex              int
		row                    [4]string
		max0, max1, max2, max3 int
	)

	if lenR = len(rows); 0 < lenR {
		rowsE = make([][4]string, lenR)

		for _, row = range rows {
			max0 = max(max0, utf8.RuneCountInString(row[0]))

			max1 = max(max1, utf8.RuneCountInString(row[1]))

			max2 = max(max2, utf8.RuneCountInString(row[2]))

			max3 = max(max3, utf8.RuneCountInString(row[3]))
		}

		for dex = range rows {
			lenR = utf8.RuneCountInString(rows[dex][0])

			rowsE[dex][0] = rows[dex][0] + strings.Repeat(" ", max0-lenR)

			lenR = utf8.RuneCountInString(rows[dex][1])

			rowsE[dex][1] = rows[dex][1] + strings.Repeat(" ", max1-lenR)

			lenR = utf8.RuneCountInString(rows[dex][2])

			rowsE[dex][2] = strings.Repeat(" ", max2-lenR) + rows[dex][2]

			rowsE[dex][3] = rows[dex][3]
		}
	}

	return
}

func (prf *Prf) Flatten() (lnsF []*Line) {
	var (
		lnsI   []*Line
		prfI   *Prf
		dexF   int
		lnF    *Line
		has    bool
		traceJ map[*Line]bool
	)

	lnsF = append(lnsF, prf.lns...)

	for _, prfI = range prf.prfsI {
		lnsI = prfI.Flatten()

		for dexF, lnF = range lnsF {
			if !IsDischargeRule(lnF.rule) {
				continue
			}

			traceJ, _ = lnF.TraceJusts(false)

			if has = slices.ContainsFunc(lnsI, func(lnI *Line) (con bool) { con = traceJ[lnI]; return }); has {
				lnsF = slices.Insert(lnsF, dexF, lnsI...)

				break
			}
		}

		if !has {
			lnsF = append(lnsF, lnsI...)
		}
	}

	return
}

func (prf *Prf) FitchFormat() (fitch string) {
	var (
		lns             []*Line
		lenL, dex, numJ int
		rows            [][4]string
		lnToDex         map[*Line]int
		ln, j1, j2, j3  *Line
	)

	lns = prf.Flatten()

	if lenL = len(lns); 0 < lenL {
		rows, lnToDex = make([][4]string, lenL), map[*Line]int{}

		for dex, ln = range lns {
			lnToDex[ln] = dex + 1

			// The first index houses the line number.
			rows[dex][0] = fmt.Sprintf("%d.", dex+1)

			// The second index holds the line and proof depth (represented by repeating '|' characters).
			if 0 < ln.prf.depthP {
				rows[dex][1] += fmt.Sprintf("%s%s", strings.Repeat("| ", ln.prf.depthP), ln.wff.String())
			} else {
				rows[dex][1] += fmt.Sprintf("%s", ln.wff.String())
			}

			// The third index holds the justification for the line.
			if ln.rule == Ass { // Assumptions receive accompanying purposes.
				// The colon anticipates the wffG in the fourth index.
				rows[dex][2] = fmt.Sprintf("%s%s", ruleToString[ln.rule], ruleToString[ln.prf.purp])
			} else {
				rows[dex][2] = fmt.Sprintf("%s", ruleToString[ln.rule])
			}

			j1, j2, j3, numJ = ln.Justs()

			switch numJ {
			case 3:
				if IsDischargeRule(ln.rule) {
					rows[dex][2] += fmt.Sprintf("(%d,%d-%d)", lnToDex[j1], lnToDex[j2], lnToDex[j3])
				} else {
					rows[dex][2] += fmt.Sprintf("(%d,%d,%d)", lnToDex[j1], lnToDex[j2], lnToDex[j3])
				}
			case 2:
				if IsDischargeRule(ln.rule) {
					rows[dex][2] += fmt.Sprintf("(%d-%d)", lnToDex[j1], lnToDex[j2])
				} else {
					rows[dex][2] += fmt.Sprintf("(%d,%d)", lnToDex[j1], lnToDex[j2])
				}
			case 1:
				rows[dex][2] += fmt.Sprintf("(%d)", lnToDex[j1])
			}

			// The fourth index holds the wffG of an inner proof.
			if ln.rule == Ass {
				rows[dex][3] = fmt.Sprintf("⊢ %s", ln.prf.wffG.String())
			}
		}
	}

	rows = equalizeCellWidths(rows)

	for dex = range rows {
		fitch += fmt.Sprintf("%s %s %s %s\n", rows[dex][0], rows[dex][1], rows[dex][2], rows[dex][3])
	}

	return
}
