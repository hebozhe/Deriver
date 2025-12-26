package fmla

func NewAtomicWff(pc Predicate, acs ...Argument) (wff *WffTree) {
	var (
		lenA int
	)

	if lenA = len(acs); pc == Equals && lenA != 2 {
		panic("Equals predicate requires exactly two arguments.")
	}

	wff = &WffTree{
		kind: Atomic,
		mop:  NoSymbol,
		pred: pc,
		args: argsToArgString(acs...),
	}

	return
}

func buildTupsAtArity(domA uint, arity uint) (tups [][]Argument, lenT uint) {
	var (
		dexA            uint
		tupsL, tupsR    [][]Argument
		tupL, tupR, tup []Argument
	)

	switch {
	case domA*arity == 0:
		tups = [][]Argument{}
	case arity == 1:
		for dexA < domA {
			tups = append(tups, []Argument{ArgConsts[dexA]})

			dexA += 1
		}
	default:
		tupsL, _ = buildTupsAtArity(domA, 1)

		tupsR, _ = buildTupsAtArity(domA, arity-1)

		for _, tupL = range tupsL {
			for _, tupR = range tupsR {
				tup = make([]Argument, arity)
				tup[0] = tupL[0]
				copy(tup[1:], tupR)

				tups = append(tups, tup)
			}
		}
	}

	lenT = uint(len(tups))

	return
}

func BuildAtomicWffs(domP uint, domA uint, arity uint) (wffs chan *WffTree) {
	domP, domA = min(domP, 20), min(domA, 20)

	wffs = make(chan *WffTree)

	switch domP {
	case 0:
		go func() {
			wffs <- NewAtomicWff(Top)

			wffs <- NewAtomicWff(Bot)

			close(wffs)
		}()
	default:
		go func(dP, dA, ity uint) {
			var (
				pcs  []Predicate
				pc   Predicate
				tups [][]Argument
				lenT uint
				tup  []Argument
			)

			pcs = append([]Predicate{}, PredConsts[:dP]...)

			tups, lenT = buildTupsAtArity(dA, ity)

			switch lenT {
			case 0:
				for _, pc = range pcs {
					wffs <- NewAtomicWff(pc)
				}
			default:
				for _, pc = range pcs {
					for _, tup = range tups {
						wffs <- NewAtomicWff(pc, tup...)
					}
				}
			}

			if ity == 2 {
				for _, tup = range tups {
					wffs <- NewAtomicWff(Equals, tup...)
				}
			}

			close(wffs)
		}(domP, domA, arity)
	}

	return
}

func BuildMixedAtomicWffs(maxDomP uint, maxDomA uint, maxArity uint) (wffs chan *WffTree) {

	wffs = make(chan *WffTree)

	go func(mdP, mdA, mIty uint) {
		var (
			ity   uint
			pwffs chan *WffTree
			pwff  *WffTree
		)

		// Get Top and Bot.
		pwffs = BuildAtomicWffs(0, 0, 0)

		for pwff = range pwffs {
			wffs <- pwff
		}

		// Get 0-place predicates.
		if 0 < mdP {
			pwffs = BuildAtomicWffs(mdP, 0, 0)

			for pwff = range pwffs {
				wffs <- pwff
			}

			if 0 < mdA {
				for ity = 0; !(mIty < ity); ity += 1 {
					if ity*mdA == 0 {
						continue
					}

					pwffs = BuildAtomicWffs(mdP, mdA, ity)

					for pwff = range pwffs {
						wffs <- pwff
					}
				}
			}
		}

		close(wffs)
	}(maxDomP, maxDomA, maxArity)

	return
}
