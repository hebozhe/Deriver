"""
This module houses all of the inference rules that are allowed in Deriver.
"""
from itertools import product
import re
from typing import Callable, Generator, Sequence
from wfftree import WffTree, has_mop
from goals import Goal, inst
from line import Line, find_valid_prems
from primitives import (
    ALL,
    AND,
    EQ,
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
    Rulable,
)


def add_sm(proof: list[Line], goals: list[Goal]) -> list[Line]:
    """
    Add an assumption to a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.
        goals (list[Goal]): The list of goals.

    Returns:
        list[Line]: The updated proof updated with a fitting assumption, if any.
    """
    last_ln: Line = (
        proof[-1]
        if proof
        else Line(
            lnum=0,
            depth=0,
            tree=WffTree(wff=VER),
            rule="",
            jstlns=tuple(),
            gics="".join(c for c in str(goals[0].tree) if c in ITEM_CONSTS),
            gPcs="".join(c for c in str(goals[0].tree) if c in PRED_CONSTS),
        )
    )

    for gol in goals:
        if gol.depth != last_ln.depth:
            continue
        if not gol.gid.endswith("S"):
            continue
        lnum: int = last_ln.lnum + 1
        depth: int = last_ln.depth + 1
        tree: WffTree = gol.tree
        rule: str = gol.gid[-2:]
        jstlns: tuple[int, ...] = tuple()
        gics: str = last_ln.gics
        gPcs: str = last_ln.gPcs
        return proof + [Line(*(lnum, depth, tree, rule, jstlns, gics, gPcs))]

    return proof


def make_drv(proof: list[Line], tree: WffTree, rule: str, jst: Sequence[Line]) -> Line:
    """
    Make a new derivation line given the proof, the intended derivation tree,
    the rule justifying it, and the premises that justify the rule.

    Args:
        proof (list[Line]): The sorted lines of a nonempty proof.
        tree (WffTree): The derivation, expressed as a WffTree.
        rule (str): The name of the inference rule that legitimizes the creation of the line.
        jst (Sequence[Line]): The Line objects that legitimize the inference rule.

    Returns:
        Line: The newly created line.
    """
    lnum: int = proof[-1].lnum + 1

    depth: int = proof[-1].depth
    dis_rules: tuple[str, ...] = (
        f"{THEN}I",
        f"{NOT}I",
        f"{ALL}I",
        f"{SOME}E",
        f"{NEC}I",
        f"{POSS}E",
    )
    depth += int(rule.endswith("S") or "/" in rule) - int(rule in dis_rules)

    jstlns: tuple[int, ...] = tuple(p.lnum for p in jst)

    gics: str = proof[-1].gics
    gPcs: str = proof[-1].gPcs

    return Line(*(lnum, depth, tree, rule, jstlns, gics, gPcs))


def gen_prem_combos(
    prems: list[Line], size: int
) -> Generator[tuple[Line, ...], None, None]:
    """
    Generate combinations of premises in a proof.

    Args:
        prems (list[Line]): A sequence of valid premise lines.
        size (int): The length of the combinations to be generated.

    Yields:
        tuple[Line, ...]: The combinations of lines.

    Returns:
        None
    """
    for combo in product(*[prems for _ in range(size)]):
        yield combo

    return None


def and_elim(proof: list[Line]) -> list[Line]:
    """
    Perform all conjunction eliminations in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{AND}E"
    drv: Line

    for prx in prems:
        if not has_mop(tree=prx.tree, mop=AND):
            continue
        if all(prx.tree.left != p.tree for p in prems):  # No left redundancy.
            drv = make_drv(proof=proof, tree=prx.tree.left, rule=rule, jst=(prx,))
            return proof + [drv]
        if all(prx.tree.right != p.tree for p in prems):  # No right redundancy.
            drv = make_drv(proof=proof, tree=prx.tree.right, rule=rule, jst=(prx,))
            return proof + [drv]

    return proof


def and_intro(proof: list[Line], goals: list[Goal]) -> list[Line]:
    """
    Perform all allowed and needed conjunction introductions in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.
        goals (list[Goal]): The list of goals.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{AND}I"
    drv: Line

    for gol in goals:
        if not has_mop(tree=gol.tree, mop=AND):
            continue
        if any(gol.tree == p.tree for p in prems):  # No redundancy.
            continue
        for prx, pry in gen_prem_combos(prems=prems, size=2):
            if prx.tree != gol.tree.left or pry.tree != gol.tree.right:
                continue
            drv = make_drv(proof=proof, tree=gol.tree, rule=rule, jst=(prx, pry))
            return proof + [drv]

    return proof


def or_elim(proof: list[Line]) -> list[Line]:
    """
    Perform all disjunction eliminations in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{OR}E"
    drv: Line

    for prx, pry, prz in gen_prem_combos(prems=prems, size=3):
        if not has_mop(tree=prx.tree, mop=OR):
            continue
        if not has_mop(tree=pry.tree, mop=THEN):
            continue
        if not has_mop(tree=prz.tree, mop=THEN):
            continue
        if pry.tree.right != prz.tree.right:  # y'z and z's consequents must match.
            continue
        if pry.tree.left != prx.tree.left:  # y's antecedent must match x's left.
            continue
        if prz.tree.left != prx.tree.right:  # z's antecedent must match x's right.
            continue
        if any(prz.tree.right == p.tree for p in prems):  # No redundancy.
            continue
        drv = make_drv(proof=proof, tree=prz.tree.right, rule=rule, jst=(prx, pry, prz))
        return proof + [drv]

    return proof


def or_intro(proof: list[Line], goals: list[Goal]) -> list[Line]:
    """
    Perform all allowed and needed disjunction introductions in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.
        goals (list[Goal]): The list of goals.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{OR}I"
    drv: Line

    for gol in goals:
        if not has_mop(tree=gol.tree, mop=OR):
            continue
        if any(gol.tree == p.tree for p in prems):  # No redundancy.
            continue
        for prx in prems:
            # x must match goal's left or right.
            if prx.tree != gol.tree.left and prx.tree != gol.tree.right:
                continue
            drv = make_drv(proof=proof, tree=gol.tree, rule=rule, jst=(prx,))
            return proof + [drv]

    return proof


def then_elim(proof: list[Line]) -> list[Line]:
    """
    Perform all conditional eliminations in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{THEN}E"
    drv: Line

    for prx, pry in gen_prem_combos(prems=prems, size=2):
        if not has_mop(tree=prx.tree, mop=THEN):
            continue
        if pry.tree != prx.tree.left:  # y must match x's antecedent.
            continue
        if any(prx.tree.right == p.tree for p in prems):  # No redundancy.
            continue
        drv = make_drv(proof=proof, tree=prx.tree.right, rule=rule, jst=(prx, pry))
        return proof + [drv]

    return proof


def deepest_sm_block(prems: list[Line]) -> list[Line]:
    """
    Find the deepest open assumption block among the legal premises.

    Args:
        prems (list[Line]): The ordered list of usable premises in a proof.

    Returns:
        list[Line]: The deepest assumption block,
            that matching the depth of the last line of the premises.
    """
    if not prems:
        return []

    last_depth: int = prems[-1].depth

    if last_depth == 0:
        return []

    for dex, prem in enumerate(reversed(prems), start=1):
        if prem.rule.endswith("S") or "/" in prem.rule:
            return prems[-dex:]

    return []


def then_intro(proof: list[Line], goals: list[Goal]) -> list[Line]:
    """
    Perform all allowed and needed conditional introductions in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.
        goals (list[Goal]): The list of goals.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{THEN}I"
    drv: Line

    sm_block: list[Line] = deepest_sm_block(prems=prems)
    if not sm_block or not sm_block[0].rule.startswith(THEN):
        return proof

    sm_line: Line = sm_block[0]
    smd: int = sm_line.depth
    for gol in goals:
        if not has_mop(tree=gol.tree, mop=THEN):
            continue
        if gol.tree.left != sm_line.tree:  # The antecedent must match the assumption.
            continue
        if gol.depth != smd - 1:  # Must match the intended depth.
            continue
        for prx in sm_block[1:]:
            if gol.tree.right != prx.tree:  # The consequent must be in the block.
                continue
            drv = make_drv(proof=proof, tree=gol.tree, rule=rule, jst=(sm_line, prx))
            return proof + [drv]

        # Consider reiterating lines that matched before the block.
        reit: Line
        for prx in prems:
            if gol.tree.right == prx.tree:  # The consequent is prior to the block.
                reit = make_drv(proof=proof, tree=prx.tree, rule="R", jst=(prx,))
                return then_intro(proof + [reit], goals)

    return proof


def iff_elim(proof: list[Line]) -> list[Line]:
    """
    Perform all biconditional eliminations in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{IFF}E"
    drv: Line

    drv_wff: str
    drv_tree: WffTree
    for prx in prems:
        if not has_mop(tree=prx.tree, mop=IFF):
            continue
        drv_wff = f"({str(prx.tree.left)}){THEN}({str(prx.tree.right)})"
        drv_tree = WffTree(wff=drv_wff)
        if all(drv_tree != p.tree for p in prems):  # No redundancy.
            drv = make_drv(proof=proof, tree=drv_tree, rule=rule, jst=(prx,))
            return proof + [drv]
        drv_wff = f"({str(prx.tree.right)}){THEN}({str(prx.tree.left)})"
        drv_tree = WffTree(wff=drv_wff)
        if all(drv_tree != p.tree for p in prems):  # No redundancy.
            drv = make_drv(proof=proof, tree=drv_tree, rule=rule, jst=(prx,))
            return proof + [drv]

    return proof


def iff_intro(proof: list[Line], goals: list[Goal]) -> list[Line]:
    """
    Perform all allowed and needed biconditional introductions in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.
        goals (list[Goal]): The list of goals.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{IFF}I"
    drv: Line

    for gol in goals:
        if not has_mop(tree=gol.tree, mop=IFF):
            continue
        if any(gol.tree == p.tree for p in prems):  # No redundancy.
            continue
        for prx, pry in gen_prem_combos(prems=prems, size=2):
            if not has_mop(tree=prx.tree, mop=THEN):
                continue
            if not has_mop(tree=pry.tree, mop=THEN):
                continue
            # x's antecedent must match y's consequent.
            if prx.tree.left != pry.tree.right:
                continue
            # x's consequent must match y's antecedent.
            if prx.tree.right != pry.tree.left:
                continue
            if prx.tree.left != gol.tree.left:
                continue
            if prx.tree.right != gol.tree.right:
                continue
            drv = make_drv(proof=proof, tree=gol.tree, rule=rule, jst=(prx, pry))
            return proof + [drv]

    return proof


def not_elim(proof: list[Line]) -> list[Line]:
    """
    Perform all negation eliminations in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{NOT}E"
    drv: Line

    drv_tree: WffTree
    for prx in prems:
        if not has_mop(tree=prx.tree, mop=NOT):
            continue
        if not has_mop(tree=prx.tree.right, mop=NOT):
            continue
        drv_tree = prx.tree.right.right
        if any(drv_tree == p.tree for p in prems):  # No redundancy.
            continue
        drv = make_drv(proof=proof, tree=drv_tree, rule=rule, jst=(prx,))
        return proof + [drv]

    return proof


def not_intro(proof: list[Line], _: list[Goal]) -> list[Line]:
    """
    Perform all allowed and needed negation introductions in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.
        _ (list[Goal]): The list of goals (irrelevant here).

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{NOT}I"
    drv: Line

    sm_block: list[Line] = deepest_sm_block(prems=prems)
    if not sm_block or not sm_block[0].rule.startswith(NOT):
        return proof

    sm_line: Line = sm_block[0]

    drv_wff: str
    drv_tree: WffTree
    for prx in sm_block[1:]:
        if str(prx.tree) != FAL:  # x must be falsum.
            continue
        drv_wff = f"{NOT}({str(sm_line.tree)})"
        drv_tree = WffTree(wff=drv_wff)
        drv = make_drv(proof=proof, tree=drv_tree, rule=rule, jst=(sm_line, prx))
        return proof + [drv]

    # Consider reiterating lines that matched before the block.
    reit: Line
    for prx in prems:
        if str(prx.tree) == FAL:  # The falsum is prior to the block.
            reit = make_drv(proof=proof, tree=prx.tree, rule="R", jst=(prx,))
            return not_intro(proof + [reit], _)

    return proof


def ver_intro(proof: list[Line], goals: list[Goal]) -> list[Line]:
    """
    Perform all allowed and needed verum introductions in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.
        goals (list[Goal]): The list of goals.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    rule: str = f"{VER}I"
    if not proof:
        if all(str(g.tree) != VER for g in goals):  # Verum must be sought.
            return proof
        v_t: WffTree = WffTree(wff=VER)
        v_tup: tuple[int, ...] = tuple()
        return [Line(*(1, 0, v_t, rule, v_tup, "", ""))]

    prems: list[Line] = find_valid_prems(lines=proof)
    drv: Line

    if any(str(p.tree) == VER for p in prems):  # No redundancy.
        return proof

    for gol in goals:
        if str(gol.tree) != VER:
            continue
        drv = make_drv(proof=proof, tree=WffTree(wff=VER), rule=rule, jst=tuple())
        return proof + [drv]

    return proof


def fal_elim(proof: list[Line], goals: list[Goal]) -> list[Line]:
    """
    Perform all falsum eliminations in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.
        goals (list[Goal]): The list of goals.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.

    Note: fal_elim is only done in response to a successful fal_intro derivation.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{FAL}E"
    drv: Line

    for gol in goals:
        if any(gol.tree == p.tree for p in prems):  # No redundancy.
            continue
        for prx in prems:
            if str(prx.tree) != FAL:
                continue
            drv = make_drv(proof=proof, tree=gol.tree, rule=rule, jst=(prx,))
            return fal_elim(proof + [drv], goals=goals)

    return proof


def fal_intro(proof: list[Line], goals: list[Goal]) -> list[Line]:
    """
    Perform all allowed and needed falsum introductions in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.
        goals (list[Goal]): The list of goals.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{FAL}I"
    drv: Line

    if any(str(p.tree) == FAL for p in prems):  # No redundancy. Call fal_elim.
        return fal_elim(proof=proof, goals=goals)

    for prx, pry in gen_prem_combos(prems=prems, size=2):
        if not has_mop(tree=pry.tree, mop=NOT):
            continue
        if prx.tree != pry.tree.right:  # x must be the assertion to negation y.
            continue
        drv = make_drv(proof=proof, tree=WffTree(wff=FAL), rule=rule, jst=(prx, pry))
        return fal_elim(proof=proof + [drv], goals=goals)  # Call fal_elim.

    return proof


def pull_prem_consts(prems: list[Line], var: str) -> str:
    """
    Pull all constants from the currently valid premises of a proof.

    Args:
        prems (list[Line]): The valid premises of a proof.
        var: The variable, used to inform whether to extract item constants or predicate constants.

    Returns:
        str: All of the unique constants.
    """
    prems_str: str = "".join(str(p.tree) for p in prems)
    if var.islower():
        return "".join({c for c in prems_str if c in ITEM_CONSTS})
    return "".join({c for c in prems_str if c in PRED_CONSTS})


def all_elim(proof: list[Line]) -> list[Line]:
    """
    Perform all universal eliminations in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{ALL}E"
    drv: Line

    drv_tree: WffTree
    for prx in prems:
        if not has_mop(tree=prx.tree, mop=ALL):
            continue
        prem_consts: str = pull_prem_consts(prems=prems, var=prx.tree.var)
        prem_consts += prx.gics if prx.tree.var.islower() else prx.gPcs
        for ppc in prem_consts:
            drv_tree = inst(tree=prx.tree, const=ppc)
            print(all_elim.__name__, str(drv_tree))
            if any(drv_tree == p.tree for p in prems):  # No redundancy.
                continue
            drv = make_drv(proof=proof, tree=drv_tree, rule=rule, jst=(prx,))
            return proof + [drv]

    return proof


def all_intro(proof: list[Line], goals: list[Goal]) -> list[Line]:
    """
    Perform all allowed and needed universal introductions in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.
        goals (list[Goal]): The list of goals.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{ALL}I"
    drv: Line

    sm_block: list[Line] = deepest_sm_block(prems=prems)
    if not sm_block or not sm_block[0].rule.startswith(ALL):
        return proof

    sm_line: Line = sm_block[0]
    smd: int = sm_line.depth
    sm_const: str = str(sm_line.tree)[1:-1]
    gol_inst: WffTree
    for gol in goals:
        if not has_mop(tree=gol.tree, mop=ALL):
            continue
        if gol.depth != smd - 1:  # Must match the intended depth.
            continue

        gol_inst = inst(tree=gol.tree, const=sm_const)

        for prx in sm_block[1:]:
            if prx.tree != gol_inst:  # x must match the goal instantiation.
                continue
            drv = make_drv(proof=proof, tree=gol.tree, rule=rule, jst=(sm_line, prx))
            return proof + [drv]

    return proof


def some_elim(proof: list[Line]) -> list[Line]:
    """
    Perform all existential eliminations in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.

    Note: This function is inelegant as fuck!
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{SOME}E"
    drv: Line

    for prx in prems:
        if not has_mop(tree=prx.tree, mop=SOME):
            continue

        # Either the assumption as been made with the instantiation, or it hasn't.
        # If it has, it will be in the premises.
        sm_: str = f"{SOME}S"
        if not any(p.rule.startswith(sm_) and prx.lnum in p.jstlns for p in prems):
            # The assumption is totally absent.
            if prx.rule in (f"{SOME}I", rule):
                # x cannot be an existential introduction or elimination.
                continue
            prem_consts: str = pull_prem_consts(prems=prems, var=prx.tree.var)
            consts: str = ITEM_CONSTS if prx.tree.var.islower() else PRED_CONSTS
            arbs: str = "".join(c for c in consts if c not in prem_consts)
            drv_tree = inst(tree=prx.tree, const=arbs[-1])
            rule = f"{SOME}S/{arbs[-1]}"  # The rule changes to an assumption.
            drv = make_drv(proof=proof, tree=drv_tree, rule=rule, jst=(prx,))
            return proof + [drv]

        # The assumption is in the premises,
        # but it may not be in the deepest assumption block.
        sm_block: list[Line] = deepest_sm_block(prems=prems)
        sm_line: Line = sm_block[0]
        if not sm_line.rule.startswith(sm_):  # The block must be of the right kind.
            continue

        sm_const: str = sm_line.rule.split("/")[-1]  # Jank as fuck!
        for pry in sm_block[1:]:
            if sm_const in str(pry.tree):  #  y must be legitimately dischargeable.
                continue
            jst: tuple[Line, ...] = (prx, sm_line, pry)
            drv = make_drv(proof=proof, tree=pry.tree, rule=rule, jst=jst)
            return proof + [drv]

    return proof


def some_intro(proof: list[Line], goals: list[Goal]) -> list[Line]:
    """
    Perform all allowed and needed existential introductions in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.
        goals (list[Goal]): The list of goals.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{SOME}I"
    drv: Line

    for gol in goals:
        if not has_mop(tree=gol.tree, mop=SOME):
            continue
        if any(gol.tree == p.tree for p in prems):  # No redundancies.
            continue
        for prx in prems:
            prem_consts: str = pull_prem_consts(prems=[prx], var=gol.tree.var)
            if all(inst(tree=gol.tree, const=c) != prx.tree for c in prem_consts):
                continue
            drv = make_drv(proof=proof, tree=gol.tree, rule=rule, jst=(prx,))
            return proof + [drv]

    return proof


def nec_elim(proof: list[Line]) -> list[Line]:
    """
    Perform all necessity eliminations in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{NEC}E"
    drv: Line

    worlds: str = "".join(c for p in prems for c in str(p.tree) if c.isdigit())
    if not worlds:
        return proof

    drv_tree: WffTree
    for prx in prems:
        if not has_mop(tree=prx.tree, mop=NEC):
            continue
        for wrl in worlds:
            drv_tree = inst(tree=prx.tree, const=wrl)
            if wrl in str(prx.tree):  # x must not already be an instantiation.
                continue
            if any(drv_tree == p.tree for p in prems):  # No redundancy.
                continue
            drv = make_drv(proof=proof, tree=drv_tree, rule=rule, jst=(prx,))
            return proof + [drv]

    return proof


def nec_intro(proof: list[Line], goals: list[Goal]) -> list[Line]:
    """
    Perform all allowed and needed necessity introductions in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.
        goals (list[Goal]): The list of goals.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{NEC}I"
    drv: Line

    sm_block: list[Line] = deepest_sm_block(prems=prems)
    if not sm_block or not sm_block[0].rule.startswith(NEC):
        return proof

    sm_line: Line = sm_block[0]
    wrl: str = str(sm_line.tree)[1:-1]
    smd: int = sm_line.depth
    for gol in goals:  # This goal is to match the right instantiation.
        if not has_mop(tree=gol.tree, mop=NEC):
            continue
        if gol.depth != smd - 1:  # Must match the intended depth.
            continue

        gol_inst = inst(tree=gol.tree, const=wrl)

        for prx in sm_block[1:]:
            if prx.tree != gol_inst:  # x must match the goal instantiation.
                continue
            drv = make_drv(proof=proof, tree=gol.tree, rule=rule, jst=(sm_line, prx))
            return proof + [drv]

    return proof


def poss_elim(proof: list[Line]) -> list[Line]:
    """
    Perform all possibility eliminations in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{POSS}E"
    drv: Line

    for prx in prems:
        if not has_mop(tree=prx.tree, mop=POSS):
            continue

        # Either the assumption as been made with the instantiation, or it hasn't.
        # If it has, it will be in the premises.
        sm_: str = f"{POSS}S"
        if not any(p.rule.startswith(sm_) and prx.lnum in p.jstlns for p in prems):
            # It's totally absent, so add one.
            if prx.rule in (f"{POSS}I", rule):
                # x cannot be a possibility introduction or elimination.
                continue
            prems_str: str = "".join(str(p.tree) for p in prems)
            warbs: str = "".join(w for w in "123456789" if w not in prems_str)
            for warb in reversed(warbs):
                drv_tree = inst(tree=prx.tree, const=warb)
                rule = f"{POSS}S/{warb}"  # The rule changes to an assumption.
                drv = make_drv(proof=proof, tree=drv_tree, rule=rule, jst=(prx,))
                return proof + [drv]

        # The assumption is in the premises,
        # but it may not be in the deepest assumption block.
        sm_block: list[Line] = deepest_sm_block(prems=prems)
        sm_line: Line = sm_block[0]
        if not prx.lnum not in sm_line.jstlns:  # The assumption is under another block.
            return proof

        # The assumption is in the block.
        # There may be a non-offending proposition in the block.
        # Use the assumption line's rule string to get the constant.
        sm_const: str = sm_line.rule.split("/")[-1]  # Jank as fuck!
        smd: int = sm_line.depth
        for pry in sm_block[1:]:
            if sm_const in str(pry.tree):  #  y must be legitimately dischargeable.
                continue
            # No redundancy.
            if any(pry.tree == p.tree and p.depth < smd for p in prems):
                continue
            jst: tuple[Line, ...] = (prx, sm_line, pry)
            drv = make_drv(proof=proof, tree=pry.tree, rule=rule, jst=jst)
            return proof + [drv]

    return proof


def poss_intro(proof: list[Line], _: list[Goal]) -> list[Line]:
    """
    Perform all allowed and needed possibility introductions in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.
        _ (list[Goal]): The list of goals (irrelevant here).

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{POSS}I"
    drv: Line

    drv_wff: str
    drv_tree: WffTree
    for prx in prems:
        stances: list[str] = re.findall(pattern=r"_\d+", string=str(prx.tree))
        if not stances:  # x must have a world in which to introduce possibility.
            continue
        last_wrl: str = stances[-1]
        drv_wff = f"{POSS}({str(prx.tree).replace(last_wrl, '')})"
        drv_tree = WffTree(wff=drv_wff)
        if any(drv_tree == p.tree for p in prems):  # No redundancy.
            continue
        drv = make_drv(proof=proof, tree=drv_tree, rule=rule, jst=(prx,))
        return proof + [drv]

    return proof


def eq_elim(proof: list[Line]) -> list[Line]:
    """
    Perform all identity eliminations in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    if not proof:
        return proof
    prems: list[Line] = find_valid_prems(lines=proof)
    rule: str = f"{EQ}E"
    drv: Line

    drv_wff: str
    drv_tree: WffTree
    l_arg: str
    r_arg: str
    for prx, pry in gen_prem_combos(prems=prems, size=2):
        if not has_mop(tree=prx.tree, mop=EQ):
            continue
        l_arg, r_arg = prx.tree.args
        if l_arg in str(pry.tree):  # Left-right substitution is allowed.
            drv_wff = str(pry.tree).replace(l_arg, r_arg)
            drv_tree = WffTree(wff=drv_wff)
            if any(drv_tree == p.tree for p in prems):  # No redundancy.
                continue
            drv = make_drv(proof=proof, tree=drv_tree, rule=rule, jst=(prx, pry))
            return proof + [drv]
        if r_arg in str(pry.tree):  # Right-left substitution is allowed.
            drv_wff = str(pry.tree).replace(r_arg, l_arg)
            drv_tree = WffTree(wff=drv_wff)
            if any(drv_tree == p.tree for p in prems):  # No redundancy.
                continue
            drv = make_drv(proof=proof, tree=drv_tree, rule=rule, jst=(prx, pry))
            return proof + [drv]

    return proof


def eq_intro(proof: list[Line], goals: list[Goal]) -> list[Line]:
    """
    Perform all allowed and needed identity introductions in a proof.

    Args:
        proof (list[Line]): The sorted lines of a proof.
        goals (list[Goal]): The list of goals.

    Returns:
        list[Line]: The updated proof, if any instances of the rule can be applied.
    """
    rule: str = f"{EQ}I"
    if not proof:
        for gol in goals:
            if not has_mop(tree=gol.tree, mop=EQ):
                continue
            if gol.tree.args[0] != gol.tree.args[-1]:  # The identity args must match.
                continue
            gics: str = proof[-1].gics
            gPcs: str = proof[-1].gPcs
            dumb_tup: tuple[int, ...] = tuple()
            return [Line(*(1, 0, gol.tree, rule, dumb_tup, gics, gPcs))]
        return proof

    prems: list[Line] = find_valid_prems(lines=proof)
    drv: Line

    for gol in goals:
        if not has_mop(tree=gol.tree, mop=EQ):
            continue
        if any(gol.tree == p.tree for p in prems):  # No redundancy.
            continue
        if gol.tree.args[0] != gol.tree.args[-1]:  # The identity args must match.
            continue
        drv = make_drv(proof=proof, tree=gol.tree, rule=rule, jst=tuple())
        return proof + [drv]

    return proof


ELIM_RULES: dict[Rulable, Callable[[list[Line]], list[Line]]] = {
    # Unused.
    VER: lambda proof: proof,
    FAL: lambda proof: proof,
    # One premise.
    AND: and_elim,
    NOT: not_elim,
    ALL: all_elim,
    NEC: nec_elim,
    # Two premises.
    THEN: then_elim,
    IFF: iff_elim,
    EQ: eq_elim,
    # Three premises.
    OR: or_elim,
    SOME: some_elim,
    POSS: poss_elim,
}

INTRO_RULES: dict[Rulable, Callable[[list[Line], list[Goal]], list[Line]]] = {
    # Zero premises.
    VER: ver_intro,
    EQ: eq_intro,
    # One premise.
    OR: or_intro,
    SOME: some_intro,
    POSS: poss_intro,
    # Two premises.
    AND: and_intro,
    FAL: fal_intro,
    IFF: iff_intro,
    THEN: then_intro,
    NOT: not_intro,
    ALL: all_intro,
    NEC: nec_intro,
}


if __name__ == "__main__":
    print(Rulable)
