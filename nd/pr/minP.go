package pr

func markUsedLines(lnG *Line) (lnsM map[*Line]struct{}) {
	var (
		lnsJ1, lnsJ2, lnsJ3 map[*Line]struct{}
		lnJ                 *Line
	)

	lnsM = map[*Line]struct{}{
		lnG: {},
	}

	if lnG.j1 != nil {
		lnsJ1 = markUsedLines(lnG.j1)
	}

	if lnG.j2 != nil {
		lnsJ2 = markUsedLines(lnG.j2)
	}

	if lnG.j3 != nil {
		lnsJ3 = markUsedLines(lnG.j3)
	}

	for lnJ = range lnsJ1 {
		lnsM[lnJ] = struct{}{}
	}

	for lnJ = range lnsJ2 {
		lnsM[lnJ] = struct{}{}
	}

	for lnJ = range lnsJ3 {
		lnsM[lnJ] = struct{}{}
	}

	return
}

func reduceLines(prf *Proof, lnsM map[*Line]struct{}) (kept uint) {
	var (
		lenL int
		lnsK []*Line
		ln   *Line
		ok   bool
		prfI *Proof
	)

	lenL = len(prf.lns)

	lnsK = make([]*Line, 0, lenL)

	for _, ln = range prf.lns {
		if _, ok = lnsM[ln]; ok {
			lnsK = append(lnsK, ln)
		}
	}

	prf.lns = lnsK

	kept = uint(len(prf.lns))

	for _, prfI = range prf.inner {
		kept += reduceLines(prfI, lnsM)
	}

	return
}

func reduceProofs(prf *Proof, lnsM map[*Line]struct{}) (kept uint) {
	var (
		prfI  *Proof
		prfsK []*Proof
		ok    bool
		ln0   *Line
		lenL  int
	)

	for _, prfI = range prf.inner {
		// Keep an inner proof only if the subproof's first line (assumption) is marked.
		if lenL = len(prfI.lns); 0 < lenL {
			ln0 = prfI.lns[0]

			// Every inner proof's first line is marked
			// in all instances of its justified use in an outer proof.
			_, ok = lnsM[ln0]
		} else {
			ok = false
		}

		if ok {
			prfsK = append(prfsK, prfI)
		}
	}

	prf.inner = prfsK

	kept = uint(len(prf.inner))

	for _, prfI = range prf.inner {
		kept += reduceProofs(prfI, lnsM)
	}

	return
}

func (prf *Proof) UpdateDexesAndPIDs() (ok bool) {
	var (
		dex int
		pid []uint
	)

	for dex = range prf.lns {
		prf.lns[dex].dex = uint(dex)
	}

	for dex = range prf.inner {
		pid = append([]uint{}, prf.pid...)
		pid = append(pid, uint(dex))

		prf.inner[dex].pid = pid

		_ = prf.inner[dex].UpdateDexesAndPIDs()
	}

	return
}

func (prf *Proof) Minimize() (lenL, lenP uint, met bool) {
	var (
		lnsM map[*Line]struct{}
		lnG  *Line
	)

	if _, lnG, met = prf.HeadGoalMet(); met {
		lnsM = markUsedLines(lnG)

		lenL = reduceLines(prf, lnsM)

		// The added 1 includes the outermost proof.
		lenP = reduceProofs(prf, lnsM) + 1

		_ = prf.UpdateDexesAndPIDs()
	}

	return
}
