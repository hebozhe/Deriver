package nd

import (
	"Deriver/fmla"
	"Deriver/nd/pr"
)

type Drv struct {
	Prf   *pr.Prf
	Syn   pr.SynBreadth
	Inf   pr.InfStrength
	Mod   pr.ModStrength
	Logic string // The name of the logic.
	rules []pr.NDRule
	Met   bool // Whether the goal of the base proof was met.
}

func NewDeriver(inf pr.InfStrength, mod pr.ModStrength, wffG *fmla.Wff, wffsP ...*fmla.Wff) (drv *Drv) {
	var (
		wffs []*fmla.Wff
		syn  pr.SynBreadth
		rule pr.NDRule
		ok   bool
	)

	wffs = append([]*fmla.Wff{wffG}, wffsP...)

	syn = pr.SynBreadthOfWffs(wffs...)

	drv = &Drv{
		Prf:   pr.NewProof(wffG, wffsP...),
		Syn:   syn,
		Inf:   inf,
		Mod:   mod,
		Logic: pr.NameLogic(inf, syn, mod),
		rules: make([]pr.NDRule, 0, pr.Elim5),
		Met:   false,
	}

	for rule = pr.TopI; ; rule += 1 {
		if _, ok = ruleToFunc[rule]; !ok {
			break
		}

		if pr.RuleFitsSynBreadth(rule, drv.Syn) && pr.RuleFitsStrengths(rule, drv.Inf, drv.Mod) {
			drv.rules = append(drv.rules, rule)
		}
	}

	return
}

func (drv *Drv) ApplyRules() (tot int) {
	var (
		rule pr.NDRule
		ndRF ndRuleFunc
		ok   bool
	)

	for _, rule = range drv.rules {
		if ndRF, ok = ruleToFunc[rule]; !ok {
			break
		}

		tot += ndRF(drv)
	}

	return
}

func (drv *Drv) DeriveAtStrength() (met bool) {
	var (
		drvG *fmla.Wff
		tot  int
	)

	drvG = drv.Prf.WffG()

	tot = 1 + goalAssume(drv.Prf, drvG, drv.Inf, drv.Mod)

	for 0 < tot && !drv.Met {
		tot = drv.ApplyRules()

		drv.Met = drv.Prf.LineWithWff(drvG) != nil
	}

	met = drv.Met

	return
}

func breadthProofSearch(st *pr.StrengthsTree, wffG *fmla.Wff, wffsP ...*fmla.Wff) (drvs []*Drv) {
	type stPair struct {
		st  *pr.StrengthsTree
		drv *Drv
	}

	var (
		stPairs        []stPair
		stE            *pr.StrengthsTree
		dexA, lenS     int
		seen, subsumed map[string]bool
		stp            stPair
		stB            *pr.StrengthsTree
	)

	stPairs = []stPair{{st: st, drv: NewDeriver(st.Inf, st.Mod, wffG, wffsP...)}}

	seen = map[string]bool{st.Name: true}

	// BFS through the strengths tree, from the strongest logic down to weaker ones.
	// Whenever a logic derives the goal, queue its weakened children for exploration.
	for dexA, lenS = 0, 1; dexA < lenS; dexA, lenS = dexA+1, len(stPairs) {
		if !stPairs[dexA].drv.DeriveAtStrength() {
			continue
		}

		_ = stPairs[dexA].drv.Prf.Prune()

		// fmt.Println(stPairs[dexA].drv.Prf.FitchFormat()) // DEBUG ONLY

		for _, stE = range stPairs[dexA].st.Branches {
			if !seen[stE.Name] {
				seen[stE.Name] = true

				stp = stPair{
					st:  stE,
					drv: NewDeriver(stE.Inf, stE.Mod, wffG, wffsP...),
				}

				stPairs = append(stPairs, stp)
			}
		}
	}

	// Drop any derivation that is subsumed by a weaker one and collect the non-subsumed derivations.
	subsumed = map[string]bool{}

	for _, stp = range stPairs {
		for _, stB = range stp.st.Branches {
			subsumed[stB.Name] = true
		}
	}

	for _, stp = range stPairs {
		if subsumed[stp.st.Name] {
			continue
		}

		drvs = append(drvs, stp.drv)
	}

	return
}

func DeriveWeakest(wffG *fmla.Wff, wffsP ...*fmla.Wff) (drvs []*Drv) {
	var (
		wffs []*fmla.Wff
		syn  pr.SynBreadth
		st   *pr.StrengthsTree
	)

	wffs = append([]*fmla.Wff{wffG}, wffsP...)

	syn = pr.SynBreadthOfWffs(wffs...)

	if st, _ = pr.NewStrengthsTree(syn); st != nil {
		drvs = breadthProofSearch(st, wffG, wffsP...)
	}

	return
}
