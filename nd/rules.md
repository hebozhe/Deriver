# Inference Rules for Natural Deduction

With respect to logical inference rules, every rule in a weaker logic (with the exception of MPL+EwC) is admissible in a stronger logic, and the strengths of the logics are, in order from weakest to strongest:

1. Implicational (T),
2. Positive (P),
3. Minimal (M),
4. Intuitionistic (I),
5. Jankov (J),
6. Gödel-Dummett (G),
7. Smetanich (S),
8. Classical (C).

All subproofs $[\dots]$ are labeled for their purposes with the format $[\dots]_{Rule}$, is the only rules that permit the discharge of a subproof. The notation $[\dots]_{(Rule~X|Rule~Y|\dots)}$, which arises only for reiteration rules, indicates that the reiterated formula may enter any subproof matching one of the subproof discharge rules.

If a subproof begins with a formula $A$, as in $[A \dots]_{Rule}$, $A$ is an assumed line at the creation of the subproof.

The _modal distance_ of a subproof increments by 1 with every modal subproof. The modal distance of the base proof is 0. The modal distance of a $Thm$ subproof increments by 2, which prevents the use of the reiteration rules ($Reit$, $Reit[C]$, $Reit[K]$) into $Thm$ subproofs.

## Propositional Logic (PL)

### Implicational Propositional Logic (TPL) Rules

- $\top I$:
  - $\vdash_{TPL} \top$
- $\to I$:
  - $[A \dots B]_{\to I} \vdash_{TPL} A \to B$
- $\to E$:
  - $A \to B, A \vdash_{TPL} B$
- $Thm$:
  - $[\top \dots A]_{Thm} \vdash_{TPL} A$
    - The modal distance from $[\top \dots A]_{Thm}$ to its immediate superproof is 2.
      - This prevents the use of the reiteration rules ($Reit$, $Reit[C]$, $Reit[K]$) into $Thm$ subproofs.

In Fitch-style proofs:

- $Reit$:
  - $A, [\dots]_{(\to I|\neg I|\forall I|\exists E)} \vdash_{TPL} [\dots A]_{(\to I|\neg I|\forall I|\exists E)}$
    - The modal distance from $A$ to $[\dots]_{(\to I|\neg I|\forall I|\exists E)}$ is 0.

**Note: While $Reit$ permits reiteration into $\neg I$, $\forall I$, and $\exists E$ subproofs, it only activates for $\neg I$ subproofs in minimal propositional logic (MPL) and for $\forall I$ and $\exists E$ subproofs in positive quantificational logics (P1QL or P2QL).**

### Positive Propositional Logic (PPL) Rules

- $\wedge I$:
  - $A, B \vdash_{PPL} A \wedge B$
- $\wedge E$:
  - $A \wedge B \vdash_{PPL} A$
  - $A \wedge B \vdash_{PPL} B$
- $\vee I$:
  - $A \vdash_{PPL} A \vee B$
  - $A \vdash_{PPL} B \vee A$
- $\vee E$:
  - $A \vee B, A \to C \vdash_{PPL} C \vee B$
  - $A \vee B, B \to C \vdash_{PPL} A \vee C$
  - $A \vee A, A \to B \vdash_{PPL} B$
- $\leftrightarrow I$:
  - $A \to B, B \to A \vdash_{PPL} A \leftrightarrow B$
- $\leftrightarrow E$:
  - $A \leftrightarrow B \vdash_{PPL} A \to B$
  - $A \leftrightarrow B \vdash_{PPL} B \to A$

### Minimal Propositional Logic (MPL) Rules

- $\bot I$:
  - $A, \neg A \vdash_{MPL} \bot$
- $\neg I$:
  - $[A \dots \bot]_{\neg I} \vdash_{MPL} \neg A$

### Intuitionistic Propositional Logic (IPL) Rules

- $\bot E$:
  - $\bot \vdash_{IPL} A$

### Jankov Propositional Logic (JPL) Rules

JPL grants that $\vdash_{JPL} \forall \Phi(\neg \Phi \vee \neg \neg \Phi)$.

- $Jan$:
  - $\neg A \to B \vdash_{JPL} \neg \neg A \vee B$

### Gödel-Dummett Propositional Logic (GPL) Rules

GPL grants that $\vdash_{GPL} \forall \Phi \forall \Psi((\Phi \to \Psi) \vee (\Psi \to \Phi))$.

- $Göd$:
  - $(A \to B) \to C \vdash_{GPL} (B \to A) \vee C$

### Smetanich Propositional Logic (SPL) Rules

SPL grants that $\vdash_{SPL} \forall \Phi \forall \Psi((\Phi \to \Psi) \vee (\Phi \vee \neg \Psi))$.

- $Sme$:
  - $(A \to B) \to C \vdash_{SPL} (A \vee \neg B) \vee C$

### Classical Propositional Logic (CPL) Rules

- $\neg E$:
  - $\neg \neg A \vdash_{CPL} A$

## N-ary Predicate Logic (NL)

### Implicational N-ary Predicate Logic with Identity (TNLi) Rules

Notational conventions:

1. The elements of $\{\Phi, \Psi, \dots\}$ refer to well-formed formulae of NL or QL.
2. $\Phi(\psi)$ refers to any $\Phi$ _with_ the argument or variable $\psi$.
3. $\Phi(\cancel\psi)$ refers to any $\Phi$ _without_ the argument or variable $\psi$.
4. $\Phi(\psi/\chi)$ refers to the replacement of arguments or variables $\psi$ with arguments or variables $\chi$ in the formula $\Phi$.

- $=I$:
  - $\vdash_{TNLi} a=a$
- $=E$:
  - $a=b, \Phi(a) \vdash_{TNLi} \Phi(b/a)$
    - $\Phi(b/a)$ may replace one or more $b$ with $a$ in $\Phi(a)$.
    - $\Phi(b/a)$ _may not_ occur in a modal formula or subformula.

## Quantificational Logic (QL)

### Positive Quantificational Logic (PQL) Rules

- $\forall I$:
  - $[\top \dots \Phi(a)]_{\forall I} \vdash_{P1QL} \forall x \Phi(x/a)$
    - $a$ must be fresh to the inner proof.
    - $\Phi(x/a)$ must replace every $a$ with $x$.
  - $[\top \dots \Phi(A)]_{\forall I} \vdash_{P2QL} \forall X \Phi(X/A)$
    - $A$ must be fresh to the inner proof.
    - $\Phi(X/A)$ must replace every $A$ with $X$.
- $\forall E$:
  - $\forall x \Phi(x) \vdash_{P1QL} \Phi(a/x)$
    - $\Phi(a/x)$ must replace every $x$ with $a$.
  - $\forall X \Phi(X) \vdash_{P2QL} \Phi(A/X)$
    - $\Phi(A/X)$ must replace every $X$ with $A$.
- $\exists I$:
  - $\Phi(a) \vdash_{P1QL} \exists x \Phi(x/a)$
    - $\Phi(x/a)$ may replace one or more $a$ with $x$.
  - $\Phi(A) \vdash_{P2QL} \exists X \Phi(X/A)$
    - $\Phi(X/A)$ may replace one or more $A$ with $X$.
- $\exists E$:
  - $\exists x \Phi(x), [\Phi(a/x) \dots \Psi(\cancel{a})]_{\exists E} \vdash_{P1QL} \Psi(\cancel{a})$
    - $a$ must be fresh to the inner proof.
    - $\Phi(a/x)$ must replace every $x$ with $a$.
  - $\exists X \Phi(X), [\Phi(A/X) \dots \Psi(\cancel{A})]_{\exists E} \vdash_{P2QL} \Psi(\cancel{A})$
    - $A$ must be fresh to the inner proof.
    - $\Phi(A/X)$ must replace every $X$ with $A$.

## Non-Normal Modal Logics (Ew, En, Es, M, N, C)

In the minimal inferential strength or stronger, the inferential strengths from E to M are, from weakest to strongest:

1. Congruent System E with Weak Interaction (Ew),
2. Congruent System E with Negative Interaction (En),
3. Congruent System E with Strong Interaction (Es), and
4. Monotonic System M.

Weak, Negative, and Strong Interactions only activate, however, when the logic is at least as strong as MPL.

### Positive Propositional Logic with Modality Ew, En, or Es (PPL+E*)

- $\Box Con$:
  - $A \to B, B \to A \vdash_{PPL+Ew} \Box A \to \Box B$
    - $Thm$ justifies $A \to B$ and $B \to A$.
- $\Diamond Con$:
  - $A \to B, B \to A \vdash_{PPL+Ew} \Diamond A \to \Diamond B$
    - $Thm$ justifies $A \to B$ and $B \to A$.

### Minimal Propositional Logic with Modality Ew (MPL+Ew)

- $\Box Int[Ew]$:
  - $\Box \top \vdash_{MPL+Ew} \neg \Diamond \bot$
  - $\Box \bot \vdash_{MPL+Ew} \neg \Diamond \top$
- $\Diamond Int[Ew]$:
  - $\Diamond \top \vdash_{MPL+Ew} \neg \Box \bot$
  - $\Diamond \bot \vdash_{MPL+Ew} \neg \Box \top$

### Minimal Propositional Logic with Modality En (MPL+En)

- All rules from [Minimal Propositional Logic with Modality Ew (MPL+Ew)](#minimal-propositional-logic-with-modality-ew-mplew)
- $\Box Int[En]$:
  - $\Box A \vdash_{MPL+En} \neg \Diamond \neg A$
  - $\Box \neg A \vdash_{MPL+En} \neg \Diamond A$
- $\Diamond Int[En]$:
  - $\Diamond A \vdash_{MPL+En} \neg \Box \neg A$
  - $\Diamond \neg A \vdash_{MPL+En} \neg \Box A$

### Minimal Propositional Logic with Modality Es (MPL+Es)

- All rules from [Minimal Propositional Logic with Modality En (MPL+En)](#minimal-propositional-logic-with-modality-en-mplen)
- $\Box Int[Es]$:
  - $\Box A, A \to \neg B \vdash_{MPL+Es} \neg \Diamond B$
    - $Thm$ justifies $A \to \neg B$.
- $\Diamond Int[Es]$:
  - $\Diamond A, A \to \neg B \vdash_{MPL+Es} \neg \Box B$
    - $Thm$ justifies $A \to \neg B$.

### Classical Propositional Logic with Modality Ew, En, or Es (CPL+E*)

- $\Diamond I$:
  - $\neg \Box \neg A \vdash_{CPL+E*} \Diamond A$

### Positive Propositional Logic with Modality M (PPL+M)

- All rules from [Positive Propositional Logic with Modality Ew, En, or Es (PPL+E*)](#positive-propositional-logic-with-modality-ew-en-or-es-pple)
- $\Box Mon$:
  - $A \to B \vdash_{PPL+M} \Box A \to \Box B$
    - $Thm$ justifies $A \to B$.
- $\Diamond Mon$:
  - $A \to B \vdash_{PPL+M} \Diamond A \to \Diamond B$
    - $Thm$ justifies $A \to B$.
- $\Box E$:
  - $\Box A, [A \dots B]_{\Box E} \vdash_{PPL+M} \Box B$
- $\Diamond E$:
  - $\Diamond A, [A \dots B]_{\Diamond E} \vdash_{PPL+M} \Diamond B$

### Minimal Propositional Logic with Modality M (MPL+M)

- All rules from [Minimal Propositional Logic with Modality Es (MPL+Es)](#minimal-propositional-logic-with-modality-es-mples)

### Classical Propositional Logic with Modality M (CPL+M)

- All rules from [Classical Propositional Logic with Modality Ew, En, or Es (CPL+E*)](#classical-propositional-logic-with-modality-ew-en-or-es-cple)

### Positive Propositional Logic with Modality N (PPL+N)

- $\Box I$:
  - $[\top \dots A]_{\Box I} \vdash_{PPL+N} \Box A$

### Minimal Propositional Logic with Modality N (MPL+N)

- $\neg \Diamond I$:
  - $[\top \dots \neg A]_{\neg \Diamond I} \vdash_{MPL+N} \neg \Diamond A$

### Classical Propositional Logic with Modality N (CPL+N)

- All rules from [Classical Propositional Logic with Modality Ew, En, or Es (CPL+E*)](#classical-propositional-logic-with-modality-ew-en-or-es-cple)

### Positive Propositional Logic with Modality C (PPL+C)

- $\Box Agg$:
  - $\Box A, \Box B \vdash_{PPL+C} \Box (A \wedge B)$
- $Reit[C]$:
  - $\Box A, [ \dots ]_{(\Box E|\Box I|\neg \Diamond I)} \vdash_{PPL+C} [\dots A]_{(\Box E|\Box I|\neg \Diamond I)}$
    - The modal distance from $\Box A$ to $[ \dots ]_{(\Box E|\Box I|\neg \Diamond I)}$ is 1.

**Note: $Reit[C]$ only activates for PPL+MC, PPL+NC, MPL+MC, or MPL+NC.**

## Normal Modal Logic (K)

### Positive Propositional Logic with Modality K (PPL+K)

This is also known as "constructive modal logic K" (CK).

- All rules from [Positive Propositional Logic with Modality M (PPL+M)](#positive-propositional-logic-with-modality-m-pplm)
- All rules from [Positive Propositional Logic with Modality N (PPL+N)](#positive-propositional-logic-with-modality-n-ppln)
- All rules from [Positive Propositional Logic with Modality C (PPL+C)](#positive-propositional-logic-with-modality-c-pplc)
- $Reit[K]$:
  - $\Box A,[ \dots ]_{\Diamond E} \vdash_{MPL+K} [\dots A]_{\Diamond E}$
    - The modal distance from $\Box A$ to $[ \dots ]_{\Diamond E}$ is 1.

## Modal Logic Extensions (D, T, 4, B, 5)

### Positive Propositional Logic with Modality D (PPL+D)

- $D$:
  - $\Box A \vdash_{PPL+D} \Diamond A$

### Positive Propositional Logic with Modality T (PPL+T)

- $TI$:
  - $A \vdash_{PPL+T} \Diamond A$
- $TE$:
  - $\Box A \vdash_{PPL+T} A$

### Positive Propositional Logic with Modality 4 (PPL+4)

- $4I$:
  - $\Box A \vdash_{PPL+4} \Box \Box A$
- $4E$:
  - $\Diamond \Diamond A \vdash_{PPL+4} \Diamond A$

### Positive Propositional Logic with Modality B (PPL+B)

- $BI$:
  - $A \vdash_{PPL+B} \Box \Diamond A$
- $BE$:
  - $\Diamond \Box A \vdash_{PPL+B} A$

### Positive Propositional Logic with Modality 5 (PPL+5)

- $5I$:
  - $\Diamond A \vdash_{PPL+5} \Box \Diamond A$
- $5E$:
  - $\Diamond \Box A \vdash_{PPL+5} \Box A$
