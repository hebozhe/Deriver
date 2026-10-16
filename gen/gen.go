package gen

func TupSet[T comparable](tupA []T) (tupB []T) {
	var (
		setE map[T]struct{}
		ele  T
		seen bool
	)

	setE = map[T]struct{}{}

	for _, ele = range tupA {
		if _, seen = setE[ele]; !seen {
			setE[ele] = struct{}{}

			tupB = append(tupB, ele)
		}
	}

	return tupB
}

func TupDifference[T comparable](tupA, tupB []T) (tupC []T) {
	var (
		setE map[T]struct{}
		a, b T
		seen bool
	)

	setE = map[T]struct{}{}

	for _, b = range tupB {
		setE[b] = struct{}{}
	}

	for _, a = range tupA {
		if _, seen = setE[a]; !seen {
			tupC = append(tupC, a)
		}
	}

	return tupC
}
