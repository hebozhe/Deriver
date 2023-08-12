"""
This module houses the functionality to perform intuitionistically valid
distributions (and some composite rules) across composite propositions.
"""
from typing import Callable
from primitives import (
    ALL,
    AND,
    BINOPS,
    FAL,
    ITEM_CONSTS,
    NEC,
    NOT,
    OR,
    POSS,
    PRED_CONSTS,
    QUANTS,
    SOME,
    THEN,
    UNOPS,
)
from wfftree import WffTree, has_mop
from goals import Goal, inst
from line import Line, find_valid_prems
from rules import gen_prem_combos


def not_not_not_dist(proof: list[Line], prx: Line, _: Line) -> tuple[list[Line], bool]:
    """
    Perform double negation elimination on triple or greater negations.

    Args:
        proof (list[Line]): The sorted proof in which to enter the subproof.
        prx (Line): The first line serving as the premise.
        _ (Line): The second line serving as the premise (irrelevant here).

    Returns:
        tuple[list[Line], bool]: The proof itself with a bool indicating that it was updated.
    """
    prems: list[Line] = find_valid_prems(lines=proof)
    end_tree: WffTree = WffTree(wff=str(prx.tree.right.right))

    if any(p.tree == end_tree for p in prems):  # No redundancies.
        return proof, False

    _x: int = prx.lnum

    _n: int = proof[-1].lnum
    _d: int = proof[-1].depth
    sm_tup: tuple[int, ...] = tuple()
    gics: str = proof[-1].gics
    gPcs: str = proof[-1].gPcs

    tree_n3: WffTree = WffTree(wff=FAL)
    tree_n4: WffTree = prx.tree.right

    new_lines: list[Line] = [
        Line(*(_n + 1, _d + 1, end_tree.right, f"~S", sm_tup, gics, gPcs)),
        Line(*(_n + 2, _d + 2, end_tree, f"~S", sm_tup, gics, gPcs)),
        Line(*(_n + 3, _d + 2, tree_n3, f"{FAL}I", (_n + 1, _n + 2), gics, gPcs)),
        Line(*(_n + 4, _d + 1, tree_n4, f"{NOT}I", (_n + 1, _n + 3), gics, gPcs)),
        Line(*(_n + 5, _d + 1, tree_n3, f"{FAL}I", (_x, _n + 4), gics, gPcs)),
        Line(*(_n + 6, _d + 0, end_tree, f"{NOT}I", (_n + 1, _n + 5), gics, gPcs)),
    ]
    return proof + new_lines, True


def not_poss_dist(proof: list[Line], prx: Line, _: Line) -> tuple[list[Line], bool]:
    """
    Perform negation distribution across the possibility operation.

    Args:
        proof (list[Line]): The sorted proof in which to enter the subproof.
        prx (Line): The first line serving as the premise.
        _ (Line): The second line serving as the premise (irrelevant here).

    Returns:
        tuple[list[Line], bool]: The proof itself with a bool indicating that it was updated.
    """
    prems: list[Line] = find_valid_prems(lines=proof)
    end_tree: WffTree = WffTree(wff=f"{NEC}{NOT}({str(prx.tree.right.right)})")

    if any(p.tree == end_tree for p in prems):  # No redundancies.
        return proof, False

    _x: int = prx.lnum

    _n: int = proof[-1].lnum
    _d: int = proof[-1].depth
    sm_tup: tuple[int, ...] = tuple()
    gics: str = proof[-1].gics
    gPcs: str = proof[-1].gPcs

    tree_n1: WffTree = WffTree(wff="[10]")
    tree_n2: WffTree = inst(tree=prx.tree.right, const="10")
    tree_n3: WffTree = WffTree(wff=FAL)
    tree_n4: WffTree = WffTree(wff=f"{NOT}({str(tree_n2)})")

    new_lines: list[Line] = [
        Line(*(_n + 1, _d + 1, tree_n1, f"{NEC}S/10", sm_tup, gics, gPcs)),
        Line(*(_n + 2, _d + 2, tree_n2, f"{NOT}S", sm_tup, gics, gPcs)),
        Line(*(_n + 3, _d + 2, prx.tree.right, f"{POSS}I", (_n + 2,), gics, gPcs)),
        Line(*(_n + 4, _d + 2, tree_n3, f"{FAL}I", (_x, _n + 3), gics, gPcs)),
        Line(*(_n + 5, _d + 1, tree_n4, f"{NOT}I", (_n + 2, _n + 4), gics, gPcs)),
        Line(*(_n + 6, _d + 0, end_tree, f"{NEC}I", (_n + 1, _n + 5), gics, gPcs)),
    ]

    return proof + new_lines, True


def not_some_dist(proof: list[Line], prx: Line, _: Line) -> tuple[list[Line], bool]:
    """
    Perform negation distribution across the existential quantifier.

    Args:
        proof (list[Line]): The sorted proof in which to enter the subproof.
        prx (Line): The first line serving as the premise.
        _ (Line): The second line serving as the premise (irrelevant here).

    Returns:
        tuple[list[Line], bool]: The proof itself with a bool indicating that it was updated.
    """
    prems: list[Line] = find_valid_prems(lines=proof)
    end_tree: WffTree = WffTree(wff=f"{ALL}{NOT}({str(prx.tree.right.right)})")

    if any(p.tree == end_tree for p in prems):  # No redundancies.
        return proof, False

    _x: int = prx.lnum
    prems_str: str = "".join(str(p.tree) for p in prems)
    arb: str = "".join(
        c
        for c in (ITEM_CONSTS if prx.tree.var.islower() else PRED_CONSTS)
        if c not in prems_str
    )[-1]

    _n: int = proof[-1].lnum
    _d: int = proof[-1].depth
    sm_tup: tuple[int, ...] = tuple()
    gics: str = proof[-1].gics
    gPcs: str = proof[-1].gPcs

    tree_n1: WffTree = WffTree(wff=f"[{arb}]")
    tree_n2: WffTree = inst(tree=prx.tree.right, const=arb)
    tree_n3: WffTree = WffTree(wff=FAL)
    tree_n4: WffTree = WffTree(wff=f"{NOT}({str(tree_n2)})")

    new_lines: list[Line] = [
        Line(*(_n + 1, _d + 1, tree_n1, f"{ALL}S/{arb}", sm_tup, gics, gPcs)),
        Line(*(_n + 2, _d + 2, tree_n2, f"{NOT}S", sm_tup, gics, gPcs)),
        Line(*(_n + 3, _d + 2, prx.tree.right, f"{SOME}I", (_n + 2,), gics, gPcs)),
        Line(*(_n + 4, _d + 2, tree_n3, f"{FAL}I", (_x, _n + 3), gics, gPcs)),
        Line(*(_n + 5, _d + 1, tree_n4, f"{NOT}I", (_n + 2, _n + 4), gics, gPcs)),
        Line(*(_n + 6, _d + 0, end_tree, f"{ALL}I", (_n + 1, _n + 5), gics, gPcs)),
    ]

    return proof + new_lines, True


def not_then_dist(proof: list[Line], prx: Line, _: Line) -> tuple[list[Line], bool]:
    """
    Perform negation distribution across the conditional operation.

    Args:
        proof (list[Line]): The sorted proof in which to enter the subproof.
        prx (Line): The first line serving as the premise.
        _ (Line): The second line serving as the premise (irrelevant here).

    Returns:
        tuple[list[Line], bool]: The proof itself with a bool indicating that it was updated.
    """
    prems: list[Line] = find_valid_prems(lines=proof)

    sub_left: WffTree = WffTree(wff=str(prx.tree.right.left))
    sub_right: WffTree = WffTree(wff=str(prx.tree.right.right))

    end_wff_a: str = f"{NOT}{NOT}({str(sub_left)})"
    end_tree: WffTree = WffTree(wff=end_wff_a)

    _x: int = prx.lnum

    _n: int = proof[-1].lnum
    _d: int = proof[-1].depth
    sm_tup: tuple[int, ...] = tuple()
    gics: str = proof[-1].gics
    gPcs: str = proof[-1].gPcs

    tree_n3: WffTree = WffTree(wff=FAL)
    tree_n5: WffTree = prx.tree.right

    if any(p.tree == end_tree for p in prems):  # No antecedent redundancies.
        end_wff_b = f"{NOT}({str(sub_right)})"
        end_tree = WffTree(wff=end_wff_b)

    if any(p.tree == end_tree for p in prems):  # No consequent redundancies.
        return proof, False

    new_lines: list[Line] = (
        [
            Line(*(_n + 1, _d + 1, end_tree.right, f"{NOT}S", sm_tup, gics, gPcs)),
            Line(*(_n + 2, _d + 2, sub_left, f"{THEN}S", sm_tup, gics, gPcs)),
            Line(*(_n + 3, _d + 2, tree_n3, f"{FAL}I", (_n + 2, _n + 1), gics, gPcs)),
            Line(*(_n + 4, _d + 2, sub_right, f"{FAL}E", (_n + 3,), gics, gPcs)),
            Line(*(_n + 5, _d + 1, tree_n5, f"{THEN}I", (_n + 2, _n + 4), gics, gPcs)),
            Line(*(_n + 6, _d + 1, tree_n3, f"{FAL}I", (_n + 5, _x), gics, gPcs)),
            Line(*(_n + 7, _d + 0, end_tree, f"{NOT}I", (_n + 1, _n + 6), gics, gPcs)),
        ]
        if end_tree == WffTree(wff=end_wff_a)
        else [
            Line(*(_n + 1, _d + 1, end_tree.right, f"{NOT}S", sm_tup, gics, gPcs)),
            Line(*(_n + 2, _d + 2, sub_left, f"{THEN}S", sm_tup, gics, gPcs)),
            Line(*(_n + 3, _d + 2, sub_right, "R", (_n + 2,), gics, gPcs)),
            Line(*(_n + 4, _d + 1, tree_n5, f"{THEN}I", (_n + 2, _n + 3), gics, gPcs)),
            Line(*(_n + 5, _d + 1, tree_n3, f"{FAL}I", (_n + 4, _x), gics, gPcs)),
            Line(*(_n + 6, _d + 0, end_tree, f"{THEN}I", (_n + 1, _n + 5), gics, gPcs)),
        ]  # ... because it must be end_wff_b's tree.
    )

    return proof + new_lines, True


def not_and_dist(proof: list[Line], prx: Line, _: Line) -> tuple[list[Line], bool]:
    """
    Perform negation distribution across the conjunction operation.

    Args:
        proof (list[Line]): The sorted proof in which to enter the subproof.
        prx (Line): The first line serving as the premise.
        _ (Line): The second line serving as the premise (irrelevant here).

    Returns:
        tuple[list[Line], bool]: The proof itself with a bool indicating that it was updated.
    """
    prems: list[Line] = find_valid_prems(lines=proof)

    sub_left: WffTree = WffTree(wff=str(prx.tree.right.left))
    sub_right: WffTree = WffTree(wff=str(prx.tree.right.right))

    end_wff_a: str = f"({str(sub_left)}){THEN}{NOT}({str(sub_right)})"
    end_tree: WffTree = WffTree(wff=end_wff_a)

    _x: int = prx.lnum

    _n: int = proof[-1].lnum
    _d: int = proof[-1].depth
    sm_tup: tuple[int, ...] = tuple()
    gics: str = proof[-1].gics
    gPcs: str = proof[-1].gPcs

    tree_n3: WffTree = prx.tree.right
    tree_n4: WffTree = WffTree(wff=FAL)
    tree_n5: WffTree = end_tree.right

    if any(p.tree == end_tree for p in prems):  # No left-right redundancies.
        sub_left, sub_right = sub_right, sub_left
        end_wff_b = f"({str(sub_left)}){THEN}{NOT}({str(sub_right)})"
        end_tree = WffTree(wff=end_wff_b)

        tree_n3 = prx.tree.right
        tree_n4 = WffTree(wff=FAL)
        tree_n5 = end_tree.right

    if any(p.tree == end_tree for p in prems):  # No right-left redundancies.
        return proof, False

    new_lines: list[Line] = [
        Line(*(_n + 1, _d + 1, sub_left, f"{THEN}S", sm_tup, gics, gPcs)),
        Line(*(_n + 2, _d + 2, sub_right, f"{NOT}S", sm_tup, gics, gPcs)),
        Line(*(_n + 3, _d + 2, tree_n3, f"{AND}I", (_n + 1, _n + 2), gics, gPcs)),
        Line(*(_n + 4, _d + 2, tree_n4, f"{FAL}I", (_n + 3, _x), gics, gPcs)),
        Line(*(_n + 5, _d + 1, tree_n5, f"{NOT}I", (_n + 2, _n + 4), gics, gPcs)),
        Line(*(_n + 6, _d + 0, end_tree, f"{THEN}I", (_n + 1, _n + 5), gics, gPcs)),
    ]

    return proof + new_lines, True


def not_or_dist(proof: list[Line], prx: Line, _: Line) -> tuple[list[Line], bool]:
    """
    Perform negation distribution across the disjunction operation.

    Args:
        proof (list[Line]): The sorted proof in which to enter the subproof.
        prx (Line): The first line serving as the premise.
        _ (Line): The second line serving as the premise (irrelevant here).

    Returns:
        tuple[list[Line], bool]: The proof itself with a bool indicating that it was updated.
    """
    prems: list[Line] = find_valid_prems(lines=proof)

    sub_left: WffTree = WffTree(wff=str(prx.tree.right.left))
    sub_right: WffTree = WffTree(wff=str(prx.tree.right.right))

    end_wff_a: str = f"{NOT}({str(sub_left)})"
    end_tree: WffTree = WffTree(wff=end_wff_a)

    tree_n1: WffTree = sub_left
    tree_n3: WffTree = WffTree(wff=FAL)

    if any(p.tree == end_tree for p in prems):  # No left redundancies.
        end_wff_b: str = f"{NOT}({str(sub_right)})"
        end_tree = WffTree(wff=end_wff_b)

        tree_n1 = sub_right

    if any(p.tree == end_tree for p in prems):  # No right redundancies.
        return proof, False

    _x: int = prx.lnum

    _n: int = proof[-1].lnum
    _d: int = proof[-1].depth
    sm_tup: tuple[int, ...] = tuple()
    gics: str = proof[-1].gics
    gPcs: str = proof[-1].gPcs

    new_lines: list[Line] = [
        Line(*(_n + 1, _d + 1, tree_n1, f"{NOT}S", sm_tup, gics, gPcs)),
        Line(*(_n + 2, _d + 1, prx.tree.right, f"{OR}I", (_n + 1,), gics, gPcs)),
        Line(*(_n + 3, _d + 1, tree_n3, f"{FAL}I", (_n + 2, _x), gics, gPcs)),
        Line(*(_n + 4, _d + 0, end_tree, f"{NOT}I", (_n + 1, _n + 3), gics, gPcs)),
    ]

    return proof + new_lines, True


def find_dists(proof: list[Line], goals: list[Goal]) -> tuple[list[Line], list[Goal]]:
    """
    Find any distribution rules that will work; or, recommend an inferential step.
    These distributions are meant to assist Deriver with performing elimination rules.
    """
    prems: list[Line] = find_valid_prems(lines=proof)
    done: bool
    for prx, pry in gen_prem_combos(prems=prems, size=2):
        # Distributions across double negations.
        if str(prx.tree).startswith(f"{NOT}{NOT}"):
            if has_mop(tree=prx.tree.right.right, mop=NOT):  # Try ~~~A |- ~A.
                proof, done = not_not_not_dist(proof=proof, prx=prx, _=pry)
                if done:
                    break

        # Distributions across single negations.
        if has_mop(tree=prx.tree, mop=NOT):
            if not hasattr(prx.tree.right, "mop"):  # It's primitive. No distributions.
                continue
            # TODO: Is ~[]A distributable to something useful?
            if has_mop(tree=prx.tree.right, mop=POSS):  # Try ~<>A |- []~A.
                proof, done = not_poss_dist(proof=proof, prx=prx, _=pry)
                if done:
                    break
            # TODO: Is ~@xAx distributable to something useful?
            if has_mop(tree=prx.tree.right, mop=SOME):  # Try ~3xAx |- @x~Ax.
                proof, done = not_some_dist(proof=proof, prx=prx, _=pry)
                if done:
                    break
            if has_mop(tree=prx.tree.right, mop=THEN):  # Try ~(A->B) |- ~~A, ~B
                proof, done = not_then_dist(proof=proof, prx=prx, _=pry)
                if done:
                    break
            if has_mop(tree=prx.tree.right, mop=AND):  # Try ~(A/\B) |- A->~B, B->~A.
                proof, done = not_and_dist(proof=proof, prx=prx, _=pry)
                if done:
                    break
            if has_mop(tree=prx.tree.right, mop=OR):  # Try ~(A\/B) |- ~A, ~B
                proof, done = not_or_dist(proof=proof, prx=prx, _=pry)

        # Distributions across conditionals.
        # Distributions across conjunctions.
        # Distributions across disjunctions.
        # Distributions across biconditionals.
    return proof, goals


DIST_RULES: dict[str, Callable[[list[Line], list[Goal]], list[Line]]] = {}


if __name__ == "__main__":
    print(
        [
            f"{a}{b}"
            for a in f"{UNOPS}{QUANTS}{BINOPS}"
            for b in f"{UNOPS}{QUANTS}{BINOPS}"
        ]
    )
