"""
This module defines a proof line.
"""
from dataclasses import dataclass
from typing import Sequence
from primitives import ALL, NEC, NOT, POSS, SOME, THEN

from wfftree import WffTree


@dataclass(frozen=True, repr=True)
class Line:
    """
    This class houses information about a line in a proof.
    """

    lnum: int  # The number of the line in the proof.
    depth: int  # The assumption depth of the line.
    tree: WffTree
    rule: str  # The rule that justified the line.
    jstlns: tuple[int, ...]  # The lines that justify the use of the rule.


def make_line(lnum: int, tree: WffTree, rule: str, jst: Sequence[Line]) -> Line:
    """
    Make a unique line given the intended derivation, the rule justifying it,
    and the premises that justify the rule.

    Args:
        lnum (int): The line number to assign to the line.
        tree (WffTree): The derivation, expressed as a WffTree.
        rule (str): The name of the inference rule that legitimizes the creation of the line.
        jst (Sequence[Line]): The Line objects that legitimize the inference rule.

    Returns:
        Line: The newly created line.
    """
    dis_rules: tuple[str, ...] = (
        f"{THEN}I",
        f"{NOT}I",
        f"{ALL}I",
        f"{SOME}E",
        f"{NEC}I",
        f"{POSS}E",
    )
    depth: int = max(p.depth for p in jst)
    depth += int(rule.endswith("S") or ", " in rule) - int(rule in dis_rules)
    jstlns: tuple[int, ...] = tuple(p.lnum for p in jst)
    return Line(lnum=lnum, depth=depth, tree=tree, rule=rule, jstlns=jstlns)


def sort_lines(lines: Sequence[Line]) -> list[Line]:
    """
    Sort lines by their line numbers.

    Args:
        lines (Sequence[Line]): A sequence of Lines.

    Returns:
        list[Line]: The sorted lines, as a list.
    """
    return sorted(lines, key=lambda ln: ln.lnum)


def find_valid_prems(lines: Sequence[Line]) -> list[Line]:
    """
    Filter the legal premises for a given line number.

        Lines can be legal premises when:
        - The line number is less than to or equal to the last line number.
        - The line depth is lower than the depth of the line at the last line number.
        - No line number after a line has a depth lower than the one preceding it it.

    Args:
        lines (Sequence[Line]): A sorted seqence of lines to a proof.

    Returns:
        list[Line]: The valid premises present in a proof.
    """
    if not lines:
        return []
    base_depth: int = lines[-1].depth
    return find_valid_prems(
        lines=[ln for ln in lines[:-1] if ln.depth <= base_depth]
    ) + [lines[-1]]
