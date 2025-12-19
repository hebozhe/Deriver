package main

import (
	"Deriver/fmla"
	"fmt"
)

func main() {
	var (
		wffs chan *fmla.WffTree
		wff  *fmla.WffTree
	)

	wffs = fmla.BuildCompositeWffs(3, 2, 0, 0)

	wffs = fmla.KeepCanonicalWffs(wffs)

	for wff = range wffs {
		fmt.Printf("%s\n", fmla.GetWffString(wff))
	}
}
