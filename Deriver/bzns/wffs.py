"""
This module builds and tests the logic of deciding which strings are well-formed formulae.
"""
import re
from itertools import product
from typing import Generator

from primitives import (
    BINOPS,
    CONSTS,
    EQ,
    FAL,
    ITEM_CONSTS,
    ITEM_VARS,
    ITEMS,
    LOGIC_CHRS,
    LP,
    LQ,
    OPS,
    PRED_CONSTS,
    PRED_VARS,
    QUANTS,
    RP,
    RQ,
    UNOPS,
    VARS,
    VER,
)


def gen_all_fmlae(from_len: int, to_len: int) -> Generator[str, None, None]:
    """
    Generate all formulae of a given length, both ill-formed and well-formed.

    Args:
        from_len (int): The length of the initial formulae to create.
        to_len (int): The length of the final formulae to create.

    Yields:
        str: All of the of_len-long formulae.
    """
    f_chars: str = re.sub(r"[C-WZc-wz]", "", LOGIC_CHRS)
    for len_r in range(from_len, to_len + 1):
        for fmla in product(*[f_chars for _ in range(len_r)]):
            yield "".join(fmla)
    return None


def has_bad_ngram(fmla: str) -> bool:
    """
    Determine whether a formula contains an illegal ngram.

    Args:
        fmla (str): The formula whose ngrams are to be checked.

    Returns:
        bool: True if a bad ngram is found, False otherwise.
    """
    fmla = re.sub(r"\s", "", fmla)

    if fmla.count(LP) != fmla.count(RP) or fmla.count(LQ) != fmla.count(RQ):
        return True

    # rf"[^{VER}{FAL}{PRED_CONSTS}{ITEM_CONSTS}{EQ}{UNOPS}{BINOPS}
    # {QUANTS}{PRED_VARS}{ITEM_VARS}{LP}{RP}{LQ}{RQ}]"
    bad_ngrams: tuple[str, ...] = (
        # Nonsense characters:
        rf"[^{LOGIC_CHRS}]",
        # Illegal initials:
        rf"^[^{VER}{FAL}{PRED_CONSTS}{ITEM_CONSTS}{UNOPS}{QUANTS}{LP}{LQ}]",
        # Illegal finals:
        rf"[^{VER}{FAL}{PRED_CONSTS}{ITEM_CONSTS}{PRED_VARS}{ITEM_VARS}{RP}{RQ}]$",
        # Illegal bigrams:
        rf"[{VER}{FAL}][^{BINOPS}{RP}{RQ}]",
        rf"[{PRED_CONSTS}][^{ITEM_CONSTS}{BINOPS}{ITEM_VARS}{RP}{LQ}{RQ}]",
        rf"[{ITEM_CONSTS}][^{ITEM_CONSTS}{EQ}{BINOPS}{ITEM_VARS}{RP}{LQ}{RQ}]",
        rf"[{EQ}][^{ITEM_CONSTS}{ITEM_VARS}]",
        rf"[{UNOPS}][^{VER}{FAL}{CONSTS}{UNOPS}{QUANTS}{VARS}{LP}{LQ}]",
        rf"[{BINOPS}][^{VER}{FAL}{CONSTS}{UNOPS}{QUANTS}{VARS}{LP}{LQ}{RQ}]",
        rf"[{QUANTS}][^{VARS}]",
        rf"[{PRED_VARS}][^{CONSTS}{OPS}{PRED_VARS}{ITEM_VARS}{LP}{RP}{LQ}{RQ}]",
        rf"[{ITEM_VARS}][^{CONSTS}{EQ}{OPS}{QUANTS}{VARS}{LP}{RP}{LQ}{RQ}]",
        rf"[{LP}][^{VER}{FAL}{CONSTS}{UNOPS}{QUANTS}{PRED_VARS}{ITEM_VARS}{LP}{LQ}]",
        rf"[{RP}][^{BINOPS}{RP}{LQ}{RQ}]",
        rf"[{LQ}][^{VER}{FAL}{CONSTS}{UNOPS}{QUANTS}{VARS}{LP}{RP}{LQ}]",
        rf"[{RQ}][^{ITEM_CONSTS}{EQ}{BINOPS}{RP}{LQ}{RQ}]",
    )

    if any(re.search(bn, fmla) for bn in bad_ngrams):
        return True

    for char in fmla:
        if char in VARS and re.search(f"[{QUANTS}]{char}.*{char}", fmla) is None:
            return True

    return False


def is_wff(fmla: str) -> bool:
    """
    Determine whether a formula is a well-formed formula.

    Args:
        fmla (str): The formula to be tested.

    Returns:
        bool: Whether the formula can successfully abbreviate to an atomic.
    """
    # Remove whitespace.

    # NOTE: has_bad_ngram() has to be flawless so as not to fuck up the results.
    if has_bad_ngram(fmla=fmla):
        return False

    fmla = re.sub(r"\s", "", fmla)

    # Check for illegal characters.
    if re.search(rf"[^{LOGIC_CHRS}]", fmla) is not None:
        return False

    # Define some common regexes for transformation.
    atom: str = rf"[{PRED_CONSTS}][{ITEM_CONSTS}]*"
    verfal: str = rf"[{VER}{FAL}]"
    q_expr: str = rf"[{QUANTS}][{VARS}]"
    d_expr: str = rf"[{LQ}][^{LQ}{RQ}]+[{RQ}]"

    # Define the transformation rules.
    tform_rules: dict[str, str] = {
        # Equality statements.
        rf"([{ITEMS}])[{EQ}]([{ITEMS}])": r"(A\g<1>\g<2>)",
        # Final atomics and non-variable singles.
        rf"^[{UNOPS}]*{atom}$": "A",
        rf"^[{UNOPS}]*{verfal}$": "A",
        rf"^[{UNOPS}]*{atom}[{BINOPS}][{UNOPS}]*{atom}$": "A",
        rf"^[{UNOPS}]*{verfal}[{BINOPS}][{UNOPS}]*{atom}$": "A",
        rf"^[{UNOPS}]*{atom}[{BINOPS}][{UNOPS}]*{verfal}$": "A",
        rf"^[{UNOPS}]*{verfal}[{BINOPS}][{UNOPS}]*{verfal}$": "A",
        # Parenthetical atomics and non-variable singles.
        rf"[{UNOPS}]*[{LP}][{UNOPS}]*{atom}[{RP}]([^{ITEMS}]|$)": r"A\g<1>",
        rf"[{UNOPS}]*[{LP}][{UNOPS}]*{verfal}[{RP}]([^{ITEMS}]|$)": r"A\g<1>",
        rf"[{LP}][{UNOPS}]*{atom}[{BINOPS}][{UNOPS}]*{atom}[{RP}]([^{ITEMS}]|$)": r"A\g<1>",
        rf"[{LP}][{UNOPS}]*{verfal}[{BINOPS}][{UNOPS}]*{atom}[{RP}]([^{ITEMS}]|$)": r"A\g<1>",
        rf"[{LP}][{UNOPS}]*{atom}[{BINOPS}][{UNOPS}]*{verfal}[{RP}]([^{ITEMS}]|$)": r"A\g<1>",
        rf"[{LP}][{UNOPS}]*{verfal}[{BINOPS}][{UNOPS}]*{verfal}[{RP}]([^{ITEMS}]|$)": r"A\g<1>",
    }

    print(fmla, end=", ")

    prev_fmla: str = ""
    while fmla not in ("A", prev_fmla):
        prev_fmla = fmla

        # Perform instantiations of quantifiers from quantifier expressions.
        for q_match in re.finditer(q_expr, fmla):
            p_count: int = 0
            q_span: str = ""
            end: int = q_match.end(0)
            for dex, char in enumerate(fmla[end:], start=end):
                if char == LP:
                    p_count += 1
                elif char == RP:
                    p_count -= 1
                if p_count < 0:
                    q_span = fmla[end:dex]
                    break
                if p_count == 0 and char in BINOPS:
                    q_span = fmla[end:dex]
                    break
            if not q_span:
                q_span = fmla[end:]
            q_var: str = q_match.group(0)[-1]
            if q_var not in q_span:
                print(q_span, "?")
                return False
            start: int = q_match.start(0)
            fmla = (
                fmla[:start]
                + "("
                + q_span.replace(q_var, "A" if q_var.isupper() else "a")
                + ")"
                + fmla[end + len(q_span) :]
            )
            if prev_fmla != fmla:
                print(fmla, end=", ")
            break

        # Apply the declaration rules.
        for d_match in re.finditer(d_expr, fmla):
            start = d_match.start(0)
            end = d_match.end(0)
            d_span: str = fmla[start:end]
            if any(c in VARS for c in d_span):
                break
            print("SPLIT!")
            return is_wff(fmla=d_span[1:-1]) and is_wff(fmla=fmla.replace(d_span, "a"))

        # Apply the transformations rules.
        # NOTE: This must happen last to avoid things like "(A)«B»" passing.
        for pat, rep in tform_rules.items():
            fmla = re.sub(pat, rep, fmla)
            if prev_fmla != fmla:
                print(fmla, end=", ")
                break
    print(fmla)
    return fmla == "A"


if __name__ == "__main__":
    CHECK_PATH: str = f"{'/'.join(__file__.split('/')[:-1])}/wff_checks.txt"
    with open(file=CHECK_PATH, mode="a+", encoding="UTF-8") as check_file:
        check_file.seek(0)
        check_file.truncate()
        for gen_fmla in gen_all_fmlae(from_len=6, to_len=8):
            if not is_wff(fmla=gen_fmla):
                continue
            check_file.write(f"{gen_fmla}\n")
