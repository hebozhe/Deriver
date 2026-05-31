package main

import (
	"Deriver/fmla"
	"fmt"
)

func main() {
	var (
		wffs chan *fmla.Wff
		wff  *fmla.Wff
		s    string
	)

	wffs = fmla.BuildCompositeWffs(2, 2, 2, 2)

	for wff = range wffs {
		s = fmla.GetWffString(fmla.MakeCanonical(wff))

		fmt.Println(s)

		/*
			 		if strings.Contains(s, "b=a↔a=b") {
						fmt.Println("Found!")

						break
					}
		*/
	}
}
