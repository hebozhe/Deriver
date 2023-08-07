"""
This module defines all of the primitives and all of the character translations for primitives.
"""
from typing import Literal

Rulable = Literal["∧", "∨", "→", "↔", "¬", "∀", "∃", "◻", "◇", "=", "⊥", "⊤"]

# Define the symbolic operations.
ITEM_CONSTS: str = "".join(chr(n) for n in range(ord("a"), ord("t") + 1))
PRED_CONSTS: str = "".join(chr(n) for n in range(ord("A"), ord("T") + 1))
ITEM_VARS: str = "".join(chr(n) for n in range(ord("u"), ord("z") + 1))
PRED_VARS: str = "".join(chr(n) for n in range(ord("U"), ord("Z") + 1))
AND: Rulable = "∧"
OR: Rulable = "∨"
THEN: Rulable = "→"
IFF: Rulable = "↔"
NOT: Rulable = "¬"
VER: Rulable = "⊤"
FAL: Rulable = "⊥"
ALL: Rulable = "∀"
SOME: Rulable = "∃"
NEC: Rulable = "◻"
POSS: Rulable = "◇"
EQ: Rulable = "="
LP: str = "("
RP: str = ")"
LQ: str = "«"
RQ: str = "»"


# Define operator collections.
ITEMS: str = f"{ITEM_CONSTS}{ITEM_VARS}"
PREDS: str = f"{PRED_CONSTS}{PRED_VARS}"
UNOPS: str = f"{NOT}{NEC}{POSS}"
BINOPS: str = f"{THEN}{AND}{OR}{IFF}"
QUANTS: str = f"{ALL}{SOME}"

OPS: str = f"{UNOPS}{BINOPS}"
VARS: str = f"{ITEM_VARS}{PRED_VARS}"
CONSTS: str = f"{ITEM_CONSTS}{PRED_CONSTS}"

LOGIC_CHRS: str = (
    f"{VER}{FAL}{PRED_CONSTS}{ITEM_CONSTS}{EQ}{UNOPS}{BINOPS}"
    + f"{QUANTS}{PRED_VARS}{ITEM_VARS}{LP}{RP}{LQ}{RQ}"
)


# Define certain symbol conversions:
SYM_CONV: dict[str, str] = {
    "~": NOT,
    "!": NOT,
    "<->": IFF,
    "<=>": IFF,
    "->": THEN,
    "=>": THEN,
    "&": AND,
    "/\\": AND,
    "^": AND,
    "|": OR,
    "\\/": OR,
    "#T": VER,
    "#F": FAL,
    "@": ALL,
    "3": SOME,
    "[]": NEC,
    "<>": POSS,
    '"l': LQ,
    '"r': RQ,
}


RULABLE_OPS: tuple[Rulable, ...] = (
    AND,
    OR,
    THEN,
    IFF,
    NOT,
    ALL,
    SOME,
    NEC,
    POSS,
    EQ,
)


def get_rulable(prim: str) -> Rulable:
    for rbl in RULABLE_OPS:
        if prim == rbl:
            return rbl
    raise TypeError(
        f'An attempt to get a rulable operator in get_rulable used illegal string "{prim}".'
    )
