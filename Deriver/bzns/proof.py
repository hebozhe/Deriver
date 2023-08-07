"""
This module houses the steps for full proof derivations.
"""
from typing import Sequence
from primitives import AND, NOT, OR, THEN, VER
from rules import ELIM_RULES, INTRO_RULES, add_sm
from wfftree import WffTree
from line import Line
from goals import Goal, find_arbs, goal_list, sort_goals


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
    trees: list[WffTree] = [WffTree(wff=wff) for wff in wffs]
    proof: list[Line] = [
        Line(lnum=i, depth=0, tree=t, rule="P", jstlns=tuple())
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
            return [g for g in goals if not g.gid.startswith(gol.gid)]
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
            [(str(ln.tree), ln.depth, ln.rule, ln.jstlns) for ln in proof],
            sep="\n",
            end="\n\n",
        )
        if not goals:
            break

        # Attempt eliminations:
        for elim_rule in ELIM_RULES.values():
            proof = elim_rule(proof)
            aft = len(proof)
            if bef < aft:
                break

        if bef < aft:
            continue

        # Attempt introductions:
        for intro_rule in INTRO_RULES.values():
            proof = intro_rule(proof, goals)
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


if __name__ == "__main__":
    att_wffs: list[str] = [f"((A{THEN}B){THEN}A){THEN}A"]
    att_drvtn: list[Line] = derive(*init_proof(wffs=att_wffs))
    print(att_drvtn)
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
    - then_intro: 
    """
