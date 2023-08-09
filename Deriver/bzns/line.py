"""
This module defines a proof line.
"""
from dataclasses import dataclass
from typing import Sequence

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
    gics: str  # The goal-intended item constants.
    gPcs: str  # The goal-intended predicate constants.


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
