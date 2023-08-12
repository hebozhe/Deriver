"""
This module houses the steps for full proof derivations.
"""
from typing import Sequence
from primitives import (
    ALL,
    AND,
    FAL,
    IFF,
    ITEM_CONSTS,
    NEC,
    NOT,
    OR,
    POSS,
    PRED_CONSTS,
    SOME,
    THEN,
    VER,
)
from rules import ELIM_RULES, INTRO_RULES, add_sm
from wfftree import WffTree
from line import Line
from goals import Goal, find_arbs, goal_list, pop_goals, sort_goals


def init_proof(wffs: Sequence[str]) -> tuple[list[Goal], list[Line]]:
    """
    Initialize a proof using a sequence of well-formed strings.

    Args:
        wffs (Sequence[str]): A sequence of well-formed strings.

    Returns:
        tuple[list[Goal], list[Line]]: The goals and initial premises for the proof.
    """
    if not wffs:
        return ([], [])

    gics: str = "".join(c for c in wffs[-1] if c in ITEM_CONSTS)
    gPcs: str = "".join(c for c in wffs[-1] if c in PRED_CONSTS)
    dumb_tup: tuple[int, ...] = tuple()

    trees: list[WffTree] = [WffTree(wff=wff) for wff in wffs]
    proof: list[Line] = [
        Line(*(i, 0, t, "P", dumb_tup, gics, gPcs))
        for i, t in enumerate(trees[:-1], start=1)
    ]
    goals: list[Goal] = goal_list(
        g_tree=WffTree(wff=wffs[-1]), arbs=find_arbs(trees=trees)
    )
    return sort_goals(goals=goals), proof


def reduce_goals(goals: list[Goal], proof: list[Line]) -> list[Goal]:
    """
    Reduce goals as they are met by the proof.

    Args:
        goals (list[Goal]): The goals toward completion of the proof.
        proof (list[Line]): The proof as it currently stands.

    Returns:
        list[Goal]: The reduced goals.
    """
    for gol in goals:
        if gol.gid.endswith("S"):  # Don't remove assumptions until they're discharged.
            continue
        if any(gol.tree == p.tree and gol.depth >= p.depth for p in proof):
            return pop_goals(goals=goals, gid=gol.gid)
    return goals


def derive(goals: list[Goal], proof: list[Line]) -> list[Line]:
    """
    Derive the topmost goal using the lines available for proof.

    Args:
        goals (list[Goal]): The hierarchically sorted list of goals.
        proof (list[Line]): The numerically sorted lines of a proof.

    Returns:
        list[Line]:  The proof as it progressed through the derivation, either successfully or not.
    """
    bef: int = len(proof)
    aft: int = len(proof) + 1
    while any(g.gid == "" for g in goals) and bef < aft:
        bef = len(proof)

        # Reduce goals:
        goals = reduce_goals(goals=goals, proof=proof)
        print(
            "GOALS:",
            [(str(g.tree), g.depth, g.gid) for g in goals],
            "PROOF:",
            [(ln.lnum, str(ln.tree), ln.depth, ln.rule, ln.jstlns) for ln in proof],
            sep="\n",
            end="\n\n",
        )
        if not goals:
            break

        # Attempt introductions:
        for intro_rule in INTRO_RULES.values():
            proof = intro_rule(proof, goals)
            aft = len(proof)
            if bef < aft:
                break

        if bef < aft:
            continue

        # Attempt eliminations:
        for elim_rule in ELIM_RULES.values():
            proof = elim_rule(proof)
            aft = len(proof)
            if bef < aft:
                break

        if bef < aft:
            continue

        # Place an assumption, if one can be:
        proof = add_sm(proof=proof, goals=goals)
        aft = len(proof)
        if bef < aft:
            continue

    return proof


def simplify(proof: list[Line]) -> list[Line]:
    """
    Derived or not, take the proof and use the last line to reduce the proof to a simpler one.

    Args:
        proof (list[Line]): The sorted, complete proof to be simplified, meaning missing no lines.

    Returns:
        list[Line]: The simplified proof.
    """
    if not proof:
        return proof

    assert all(
        i == p.lnum for i, p in enumerate(proof, start=1)
    ), "Function simplify failed. The proof must be sorted and not missing lines."

    # Find all of the necessary dependencies.
    last_ln: Line = proof[-1]
    jst_stream: tuple[int, ...] = (last_ln.lnum,) + last_ln.jstlns
    dex = 0
    while dex < len(jst_stream):
        jst_stream += proof[jst_stream[dex] - 1].jstlns
        dex += 1

    # Set the renumber scheme.
    old_new: dict[int, int] = {
        o: n for n, o in enumerate(sorted(set(jst_stream)), start=1)
    }

    # Reduce the proof to just those in jst_stream.
    red_proof: list[Line] = [ln for ln in proof if ln.lnum in old_new.keys()]

    # Simplify the proof by recreating the lines.
    # Line objects are frozen, so they must be rebuilt.
    simp_proof: list[Line] = [
        Line(
            lnum=old_new[ln.lnum],
            depth=ln.depth,
            tree=ln.tree,
            rule=ln.rule,
            jstlns=tuple(old_new[jl] for jl in ln.jstlns),
            gics=ln.gics,
            gPcs=ln.gPcs,
        )
        for ln in red_proof
    ]

    print(
        "SIMPLIFIED PROOF:",
        [(ln.lnum, str(ln.tree), ln.depth, ln.rule, ln.jstlns) for ln in simp_proof],
        sep="\n",
        end="\n\n",
    )
    return simp_proof


if __name__ == "__main__":
    att_wffs: list[str] = [
        f"{POSS}A{THEN}{NEC}B",
        f"{NEC}(A{THEN}B)",
    ]
    att_drvtn: list[Line] = derive(*init_proof(wffs=att_wffs))
    simp_drvtn = simplify(proof=att_drvtn)

    print(att_drvtn, simp_drvtn, sep="\n\n")
    """
    Checklist:
    - and_elim: Good!
    - and_intro: Good!
    - or_elim: Good!
    - or_intro: Good!
    - not_elim: Good!
    - not_intro: Good!
    - fal_elim: Good!
    - fal_intro: Good!
    - ver_elim: NONE
    - ver_intro: Good!
    - then_elim: Good!
    - then_intro: Good!
    - iff_elim: Good!
    - iff_intro: Good!
    - all_elim: Good!
    - all_intro: Good!
    - some_elim: Good!
    - some_intro: Good!
    - nec_elim: Good!
    - nec_intro: Good!
    - poss_intro: Good!
    - poss_elim:
    """
