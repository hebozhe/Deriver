"""
This module creates proof goals for a given proposition.
"""
from dataclasses import astuple, dataclass
from typing import Sequence, TypedDict
from primitives import (
    AND,
    FAL,
    ITEM_CONSTS,
    OR,
    PRED_CONSTS,
    THEN,
    IFF,
    NOT,
    ALL,
    SOME,
    NEC,
    POSS,
    EQ,
)
from wfftree import WffTree


class ArbType(TypedDict):
    a: str
    A: str
    w: str


def find_arbs(trees: Sequence[WffTree]) -> ArbType:
    """
    Create a dictionary of all of the available arbitrary first-order,
    second-order, and modal constants for the language.

    Args:
        trees (Sequence[WffTree]): The well-formed formulae that are presumed in a proof.

    Returns:
        ArbType: A dictionary of those constants which do not presume themselves in a proof,
            categorized by their role.
    """
    fmlae: str = "".join(str(t) for t in trees)
    return ArbType(
        a="".join(c for c in ITEM_CONSTS if c not in fmlae),
        A="".join(c for c in PRED_CONSTS if c not in fmlae),
        w="".join(c for c in "123456789" if c not in fmlae),
    )


def instantiate(tree: WffTree, const: str) -> WffTree:
    """
    Instantiate every instance of the variable in a wff tree
    with its chosen arbitrary constant.

    Args:
        tree (WffTree): The well-formed formula receiving the replacement.
        const (str): The single character replacing it.
    """
    arbed_wff: str
    if const.isnumeric():  # It's a modal instantiation.
        if tree.val == 2:
            tree.left = instantiate(tree.left, const)
            tree.right = instantiate(tree.right, const)
        elif tree.val == 1:
            tree.right = instantiate(tree.right, const)
        arbed_wff = f"{str(tree)}_{const}"
        return WffTree(wff=arbed_wff)
    arbed_wff = str(tree).replace(tree.var, const)
    return WffTree(wff=arbed_wff)


@dataclass(frozen=True, repr=True)
class Goal:
    """
    This class houses data surrounding goals for proofs.
    """

    tree: WffTree  # The tree of the proof.
    arbs: ArbType  # The dictionary of available arbitrary constants as of this goal.
    gid: str  # The goal's ID
    depth: int  # The assumption depth in a proof.


def goal_list(
    g_tree: WffTree, arbs: ArbType, gid: str = "", depth: int = 0
) -> list[Goal]:
    """
    Create a main list of Goal objects from a well-formed formula.
    Normally, this will be the main derivation objective.

    # TODO: Add an ext_goal_list function as new elim rules call for derivations,
    themselves.

    Args:
        g_tree (WffTree): The "goal" formula to be derived.
        gid (str): The goal ID, which indicates the precedence of the goal in a proof.
        depth (int): The current assumption depth where the line must be for the intro rule to apply.

    Returns:
        list[Goal]: A list of all of the Goal objects.
    """
    g_mop = g_tree.mop if hasattr(g_tree, "mop") else ""
    g_a: Goal
    g_b: Goal
    new_a: WffTree
    new_b: WffTree
    gs_a: list[Goal]
    new_arb: str
    # Handle binary operators first.
    if g_mop == AND:
        g_a = Goal(tree=g_tree.left, arbs=arbs, gid=f"{gid}A", depth=depth)
        g_b = Goal(tree=g_tree.right, arbs=arbs, gid=f"{gid}B", depth=depth)
        return (
            ([Goal(g_tree, arbs, gid, depth)] if not gid else [])
            + [g_a, g_b]
            + goal_list(*astuple(g_a))
            + goal_list(*astuple(g_b))
        )
    if g_mop == OR:
        g_a = Goal(tree=g_tree.left, arbs=arbs, gid=f"{gid}A", depth=depth)
        g_b = Goal(tree=g_tree.right, arbs=arbs, gid=f"{gid}B", depth=depth)
        return (
            ([Goal(g_tree, arbs, gid, depth)] if not gid else [])
            + [g_a, g_b]
            + goal_list(*astuple(g_a))
            + goal_list(*astuple(g_b))
        )
    if g_mop == THEN:
        g_a = Goal(tree=g_tree.left, arbs=arbs, gid=f"{gid}{THEN}S", depth=depth)
        g_b = Goal(tree=g_tree.right, arbs=arbs, gid=f"{gid}{THEN}SA", depth=depth + 1)
        return (
            ([Goal(g_tree, arbs, gid, depth)] if not gid else [])
            + [g_a, g_b]
            + goal_list(*astuple(g_b))
        )
    if g_mop == IFF:
        new_a = WffTree(wff=f"({str(g_tree.left)}){THEN}({str(g_tree.right)})")
        new_b = WffTree(wff=f"({str(g_tree.right)}){THEN}({str(g_tree.left)})")
        g_a = Goal(tree=new_a, arbs=arbs, gid=f"{gid}A", depth=depth)
        g_b = Goal(tree=new_b.right, arbs=arbs, gid=f"{gid}B", depth=depth)
        return (
            ([Goal(g_tree, arbs, gid, depth)] if not gid else [])
            + [g_a, g_b]
            + goal_list(*astuple(g_a))
            + goal_list(*astuple(g_b))
        )
    # Handle unary operators next.
    if g_mop == NOT:
        new_b = WffTree(wff=FAL)
        g_a = Goal(tree=g_tree.right, arbs=arbs, gid=f"{gid}{NOT}S", depth=depth)
        g_b = Goal(tree=new_b, arbs=arbs, gid=f"{gid}{NOT}SA", depth=depth + 1)
        return (
            ([Goal(g_tree, arbs, gid, depth)] if not gid else [])
            + [g_a, g_b]
            + goal_list(*astuple(g_b))
        )
    if g_mop == ALL:
        if g_tree.var.islower():
            new_arb = arbs["a"][0]
            arbs["a"] = arbs["a"][1:]
        else:
            new_arb = arbs["A"][0]
            arbs["A"] = arbs["A"][1:]
        new_a = WffTree(wff=f"[{new_arb}]")
        new_b = instantiate(tree=g_tree.right, const=new_arb)
        g_a = Goal(tree=new_a, arbs=arbs, gid=f"{gid}{ALL}S", depth=depth)
        g_b = Goal(tree=new_b, arbs=arbs, gid=f"{gid}{ALL}SA", depth=depth + 1)
        return (
            ([Goal(g_tree, arbs, gid, depth)] if not gid else [])
            + [g_a, g_b]
            + goal_list(*astuple(g_b))
        )
    if g_mop == SOME:
        gs_a = [
            Goal(
                tree=instantiate(tree=g_tree.right, const=c),
                arbs=arbs,
                gid=f"{gid}*{c}*",
                depth=depth,
            )
            for c in (ITEM_CONSTS if g_tree.var.islower() else PRED_CONSTS)
        ]
        return (
            ([Goal(g_tree, arbs, gid, depth)] if not gid else [])
            + gs_a
            + [g for gl in [goal_list(*astuple(a)) for a in gs_a] for g in gl]
        )
    if g_mop == NEC:
        new_arb = arbs["w"][0]
        arbs["w"] = arbs["w"][1:]
        new_a = WffTree(wff=f"[{new_arb}]")
        new_b = instantiate(tree=g_tree.right, const=new_arb)
        g_a = Goal(tree=new_a, arbs=arbs, gid=f"{gid}{NEC}S", depth=depth)
        g_b = Goal(tree=new_b, arbs=arbs, gid=f"{gid}{NEC}SA", depth=depth + 1)
        return (
            ([Goal(g_tree, arbs, gid, depth)] if not gid else [])
            + [g_a, g_b]
            + goal_list(*astuple(g_b))
        )
    if g_mop == POSS:
        gs_a = [
            Goal(
                tree=instantiate(tree=g_tree.right, const=c),
                arbs=arbs,
                gid=f"{gid}*{c}*",
                depth=depth,
            )
            for c in "0123456789"
        ]
        return (
            ([Goal(g_tree, arbs, gid, depth)] if not gid else [])
            + gs_a
            + [g for gl in [goal_list(*astuple(a)) for a in gs_a] for g in gl]
        )
    if g_mop == EQ:
        l_arg: str = g_tree.args[0]
        r_arg: str = g_tree.args[-1]
        new_a = WffTree(wff=f"{l_arg}{EQ}{l_arg}")
        new_b = WffTree(wff=f"{r_arg}{EQ}{r_arg}")
        g_a = Goal(tree=new_a, arbs=arbs, gid=gid, depth=depth)
        g_b = Goal(tree=new_b, arbs=arbs, gid=gid, depth=depth)
        return [g_a, g_b]
    new_a = WffTree(wff=f"{NOT}({str(g_tree)})")
    new_b = WffTree(wff=f"{FAL}")
    g_a = Goal(tree=new_a, arbs=arbs, gid=f"{gid}{NOT}S", depth=depth)
    g_b = Goal(tree=new_b, arbs=arbs, gid=f"{gid}{NOT}SA", depth=depth + 1)
    return ([Goal(g_tree, arbs, gid, depth)] if not gid else []) + [g_a, g_b]


def sort_goals(goals: list[Goal]) -> list[Goal]:
    """
    Sort Goal items by their gid attributes.

    Args:
        goals (list[Goal]): A list of goals.

    Returns:
        list[Goal]: The sorted goals.
    """
    return sorted(goals, key=lambda g: g.gid)


def ext_goals(goals: list[Goal], new_goal: Goal) -> list[Goal]:
    """
    Extend some already defined goals with a new goal.
    """
    ext_goals: list[Goal] = goal_list(*astuple(new_goal))
    return sort_goals(goals=goals + [new_goal] + ext_goals)


def pop_goals(goals: list[Goal], gid: str) -> list[Goal]:
    """
    Remove all goals from a list if their goal IDs start with the given goal ID.
    """
    return [g for g in goals if not g.gid.startswith(gid)]


if __name__ == "__main__":
    goal_wfftree: WffTree = WffTree(wff=f"{NEC}(P∧Q)↔{NEC}(((P∨Q)↔P)↔Q)")
    gwt_list: list[Goal] = goal_list(
        g_tree=goal_wfftree, arbs=find_arbs(trees=[goal_wfftree])
    )
    gwt_list = sort_goals(goals=gwt_list)
    for row in gwt_list:
        print(row)
