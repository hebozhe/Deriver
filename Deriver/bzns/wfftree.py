"""
This module defines the WffTree object, which is the basis for a proof.
"""
from primitives import (
    FAL,
    LQ,
    OPS,
    RQ,
    LP,
    RP,
    UNOPS,
    BINOPS,
    QUANTS,
    EQ,
    PREDS,
    VER,
    Rulable,
    get_rulable,
)


def main_op(wff: str) -> tuple[int, int, str]:
    """
    Find the key main operator data of a formula.

    Args:
        wff (str): The well-formed formula from which to find the main operator.

    Returns:
        tuple[int, int, str]: The main operator's position, its parenthetical depth, and its symbol.
    """
    ops: str = f"{OPS}{QUANTS}{EQ}{PREDS}{VER}{FAL}"
    pos_cnt_op: list[tuple[int, int, str]] = [
        (
            i,
            sum(
                (int(c == LP) + int(c == LQ)) - (int(c == RP) + int(c == RQ))
                for c in wff[:i]
            ),
            o,
        )
        for i, o in enumerate(wff)
        if o in ops
    ]

    # The main operator is the one with the fewest surrounding parens and quotes.
    min_cnt: int = min(c for _, c, _ in pos_cnt_op)
    pos_cnt_op = [tup for tup in pos_cnt_op if tup[1] == min_cnt]
    if len(pos_cnt_op) == 1:
        return pos_cnt_op.pop()

    # If there are ties, the binary operator takes precedence.
    binop: list[tuple[int, int, str]] = [tup for tup in pos_cnt_op if tup[-1] in BINOPS]
    if binop:
        return binop.pop()

    # If there are no binary operators, the leftmost unary operator or quantifier takes precedence.
    unqu: str = f"{UNOPS}{QUANTS}"
    unops: list[tuple[int, int, str]] = [tup for tup in pos_cnt_op if tup[-1] in unqu]
    if unops:
        min_pos: int = min(p for p, _, _ in unops)
        unop: list[tuple[int, int, str]] = [tup for tup in unops if tup[0] == min_pos]
        return unop.pop()

    # If there are no unary operators, the equality operator takes precedence.
    eqs: list[tuple[int, int, str]] = [tup for tup in pos_cnt_op if tup[-1] in EQ]
    if eqs:
        return eqs.pop()

    # Finally, we default to the predicate, verum, or falsum.
    ptf: str = f"{PREDS}{VER}{FAL}"
    preds: list[tuple[int, int, str]] = [tup for tup in pos_cnt_op if tup[-1] in ptf]
    return preds.pop()


def clean(wff: str, pmop: str = "?") -> str:
    """
    Clean a well-formed formula, namely removing its excess parentheses.

    Args:
        wff (str): The well-formed formula whose parentheses are to be reduced.
        pmop (str): The previous main operator, used to assist recursion.

    Returns:
        str: The cleaned well-formed formu.a.
    """
    # print(wff)

    # Only remove the outermost explicitly with a loop.
    # The rest is done via recursion.
    p_counts: tuple[int, ...] = tuple(
        sum(int(c == LP) - int(c == RP) for c in wff[:i])
        for i in range(1, len(wff) + 1)
    )
    while 0 not in p_counts[:-1] and not p_counts[0] == 0:
        # print(wff, p_counts)
        wff = wff[1:-1]
        p_counts = tuple(pc - 1 for pc in p_counts[1:-1])

    # Collect the main operator data.
    pos, _, mop = main_op(wff=wff)

    if mop in f"{VER}{FAL}":
        return wff

    if mop in BINOPS:
        wff = f"{clean(wff[:pos], mop)}{mop}{clean(wff[pos+1:], mop)}"
        if pmop in f"{BINOPS}{UNOPS}{QUANTS}":
            return f"{LP}{wff}{RP}"
        return wff

    if mop in UNOPS:
        wff = f"{mop}{clean(wff[pos+1:], mop)}"
        return wff

    if mop in QUANTS:
        wff = f"{mop}{wff[pos+1]}{clean(wff[pos+2:], mop)}"

    if mop in EQ:
        if wff.startswith(LQ):
            wff = wff.replace(wff[1 : pos - 1], clean(wff[1 : pos - 1], mop))
        if wff.endswith(RQ):
            wff = wff.replace(wff[pos + 1 :], clean(wff[pos + 1 :], mop))
        return wff

    # It's a predicate.
    start: int = wff.find(LQ)
    if start > -1:
        d_count: int = 1
        for end, char in enumerate(wff[start + 1 :], start=start + 1):
            d_count += int(char == LQ) - int(char == RQ)
            if d_count != 0:
                continue
            d_span = wff[start + 1 : end]
            wff = wff.replace(d_span, clean(d_span, mop))

    return wff


class WffTree:
    """
    This class takes a well-formed formula and generates a tree.
    """

    def __init__(self, wff: str) -> None:
        # This is a special carve-out for assumption place-holders, e.g. "[a]", "[A]", "[1]"
        self.wff: str
        if len(wff) == 3 and wff[0] == "[" and wff[-1] == "]":
            self.wff = wff
            return None

        self.wff = clean(wff=wff)

        pos, _, mop = main_op(wff=self.wff)

        self.mop: Rulable  # The saved main operator.
        self.val: int  # The valency of the main operator, 0 if atomic.
        self.var: str  # The variable of the quantifier, if self.mop is in QUANTS.
        self.left: WffTree
        self.right: WffTree
        self.args: tuple[str, ...]

        if len(self.wff) == 1:  # Verum, falsum, and 0-place predicates.
            self.val = 0
            return None

        if mop in BINOPS:  # Binary sentences.
            self.mop = get_rulable(prim=mop)
            self.val = 2
            self.left = WffTree(wff=clean(wff=self.wff[:pos]))
            self.right = WffTree(wff=clean(wff=self.wff[pos + 1 :]))
            return None

        if mop in UNOPS:  # Unary sentences.
            self.mop = get_rulable(prim=mop)
            self.val = 1
            self.right = WffTree(wff=clean(wff=self.wff[pos + 1 :]))
            return None

        if mop in QUANTS:  # Quantifier sentences.
            self.mop = get_rulable(prim=mop)
            self.val = 1
            self.var = wff[pos + 1]
            self.right = WffTree(wff=clean(wff=self.wff[pos + 2 :]))
            return None

        if mop in f"{PREDS}{EQ}":  # Atomic predicates and equality.
            if mop == EQ:
                self.mop = get_rulable(prim=mop)
            self.val = 0
            self.args = tuple()

            if self.mop in EQ:
                self.args = (self.wff[:pos], self.wff[pos + 1 :])
                return None

            d_count: int = 0
            span_len: int = 1
            for end, char in enumerate(self.wff[1:], start=1):
                d_count += int(char == LQ) - int(char == RQ)
                if d_count == 0:
                    self.args += (self.wff[(end - span_len) + 1 : end + 1],)
                    span_len = 1
                else:
                    span_len += 1
            return None

        if self.mop in f"{VER}{FAL}":  # Verum and falsum.
            self.val = 0
            self.args = tuple()

    def __str__(self) -> str:
        return self.wff

    def __repr__(self) -> str:
        """
        Recursievely generate a parse tree (readable here: http://mshang.ca/syntree/).

        Returns:
            str: The square-bracket-annoted parse tree.
        """
        if not hasattr(self, "mop"):
            if hasattr(self, "args"):
                jargs: str = (
                    "] [".join(self.args) if len(self.args) > 1 else "".join(self.args)
                )
                return f"[{self.mop} [{jargs}]]"
            return f"[{self.wff}]"
        if self.mop in BINOPS:
            return f"[{self.mop} {repr(self.left)} {repr(self.right)}]"
        elif self.mop in UNOPS:
            return f"[{self.mop} {repr(self.right)}]"
        elif self.mop in QUANTS:
            return f"[{self.mop}{self.var} {repr(self.right)}]"
        else:
            return f"[{self.wff}]"

    def __eq__(self, __value: object) -> bool:
        if not isinstance(__value, WffTree):
            raise TypeError("WffTree objects must be compared to WffTree objects.")
        return self.wff == __value.wff


def has_mop(tree: WffTree, mop: Rulable) -> bool:
    """
    Check whether a given WffTree has a certain operator.

    Args:
        tree (WffTree): The object representing a well-formed formula.
        mop (Rulable): The main operator being checked.

    Returns:
        bool: False if tree either has no main operator or if it's not equal to mop,
            True otherwise.
    """
    return hasattr(tree, "mop") and tree.mop == mop


if __name__ == "__main__":
    test_wff: str = "j=k↔Aa«B»b"
    print(clean(wff=test_wff))
    print(repr(WffTree(wff=test_wff)))
    print((WffTree(wff=test_wff).right))
