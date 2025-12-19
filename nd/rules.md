# Inference Rules for Natural Deduction

## Propositional Logic (PL)

With respect to propositional logic inference rules, every rule in a weaker logic is admissible in a stronger logic.

- TPL is weaker than PPL.
- PPL is weaker than MPL.
- MPL is weaker than IPL.
- IPL is weaker than CPL.

### Trivial Propositional Logic (TPL) Rules

- $\top I$:
  - $\vdash \top$

### Positive Propositional Logic (PPL) Rules

- $\to I$:
  - $[A \dots B], \vdash A \to B$
- $\to E$:
  - $A \to B, A \vdash B$
- $\wedge I$:
  - $A, B \vdash A \wedge B$
- $\wedge E$:
  - $A \wedge B \vdash A$
  - $A \wedge B \vdash B$
- $\vee I$:
  - $A \vdash A \vee B$
  - $B \vdash A \vee B$
- $\vee E$:
  - $A \vee B, A \to C, B \to C \vdash C$
- $\leftrightarrow I$:
  - $A \to B, B \to A \vdash A \leftrightarrow B$
- $\leftrightarrow E$:
  - $A \leftrightarrow B, A \vdash B$
  - $A \leftrightarrow B, B \vdash A$

For convenience in Fitch-style proofs:

- $Reit$:
  - $A \vdash A$

### Minimal Propositional Logic (MPL) Rules

- $\bot I$:
  - $A, \neg A \vdash \bot$
- $\neg I$:
  - $[A \dots \bot] \vdash \neg A$

### Intuitionistic Propositional Logic (IPL) Rules

- $\bot E$:
  - $\bot \vdash A$

### Classical Propositional Logic (CPL) Rules

- $\neg E$:
  - $\neg \neg A \vdash A$

## Quantificational Logic (QL) Rules

- $\forall I$:
  - $A(t) \vdash \forall x A(x/t)$
    - $t$ must be arbitrary.
- $\forall E$:
  - $\forall x A(x) \vdash A(t/x)$
- $\exists I$:
  - $\exists x A(x),[A(t/x) \dots B] \vdash B$
    - $t$ must be arbitrary and absent in $B$.
- $\exists E$:
  - $A(t) \vdash \exists x A(x/t)$

## Quantificational Logic with Identity (QLi) Rules

- $=I$:
  - $\vdash t=t$
- $=E$:
  - $t=t', A(t) \vdash A(t'/t)$

## Modal Logic

The Hilbert-styled axioms, re-fashioned as rules, for minimal/intuitionistic modal logic (L+IK) are:

**Axioms:**

1. $\vdash \Box \top$
2. $\vdash \neg \Diamond \bot$
3. $\Box(A \to B) \vdash \Box A \to \Box B$
4. $\Box(A \to B) \vdash \Diamond A \to \Diamond B$
5. $\Diamond(A \vee B) \vdash (\Diamond A \vee \Diamond B)$
6. $\Diamond A \to \Box B \vdash \Box(A \to B)$

**Rules:**

- From $\vdash A$, deduce $\vdash \Box A$.
- From $A \to B$ and $A$, deduce $B$.

The equivalency $\Box A \leftrightarrow \neg \Diamond \neg A$ is not derivable in L+IK.

### Minimal/Intuitionistic Modal Logic K (L+IK) Rules

- $\Box I$:
  - $[\top @ w_{n+1} \dots A@ w_{n+1}] \vdash \Box A@ w_{n}$
- $\Box E$:
  - $\Box A@ w_{n} \vdash A@ w_{n+1}$
- $\Diamond E$:
  - $\Diamond A @ w_{n}, [A @ w_{n+1} \dots B@ w_{n+1}] \vdash \Diamond B @ w_{n}$

### Classical Modal Logic K (L+CK) Rules

- $\Diamond I$:
  - $\neg \Box A \vdash \Diamond \neg A$

### Supplemental Minimal/Intuitionistic Modal Logic K (L+IK) Rules

- $\Box \top I$:
  - $\vdash \Box \top$
- $\Box \top E$:
  - $\Box \top \vdash \top$
- $\Diamond \top I$:
  - $\vdash \Diamond \top$
- $\Diamond \top E$:
  - $\Diamond \top \vdash \top$
- $\Box \to I$:
  - $[\Diamond A \dots \Box B] \vdash \Box(A \to B)$.
- $\Box \to E$:
  - $\Box(A \to B), \Box A \vdash \Box B$.
- $\Diamond \to I$:
  - $[\Box A \dots \Diamond B] \vdash \Diamond(A \to B)$
- $\Diamond \to E$:
  - $\Diamond(A \to B), \Box A \vdash \Diamond B$.
  - $\Box(A \to B), \Diamond A \vdash \Diamond B$.
- $\Box \wedge I$:
  - $\Box A, \Box B \vdash \Box(A \wedge B)$
- $\Box \wedge E$:
  - $\Box(A \wedge B) \vdash \Box A$
  - $\Box(A \wedge B) \vdash \Box B$
- $\Diamond \wedge I$:
  - $\Diamond A, \Box B \vdash \Diamond(A \wedge B)$
  - $\Box A, \Diamond B \vdash \Diamond(A \wedge B)$
- $\Diamond \wedge E$:
  - $\Diamond(A \wedge B) \vdash \Diamond A$
  - $\Diamond(A \wedge B) \vdash \Diamond B$
- $\Box \vee I$:
  - $\Box A \vdash \Box(A \vee B)$
  - $\Box B \vdash \Box(A \vee B)$
- $\Box \vee E$:
  - $\Box(A \vee B), \Box(A \to C), \Box(B \to C) \vdash \Box C$
- $\Diamond \vee I$:
  - $\Diamond(A) \vdash \Diamond(A \vee B)$
  - $\Diamond(B) \vdash \Diamond(A \vee B)$
- $\Diamond \vee E$:
  - $\Diamond(A \vee B), \Box(A \to C), \Box(B \to C) \vdash \Diamond C$
  - $\Box(A \vee B), \Diamond(A \to C), \Box(B \to C) \vdash \Diamond C$
  - $\Box(A \vee B), \Box(A \to C), \Diamond(B \to C) \vdash \Diamond C$
- $\Box \leftrightarrow I$:
  - $\Box(A \to B),\Box(B \to A) \vdash \Box(A \leftrightarrow B)$
- $\Box \leftrightarrow E$:
  - $\Box(A \leftrightarrow B), \Box A \vdash \Box B$
  - $\Box(A \leftrightarrow B), \Box B \vdash \Box A$
- $\Diamond \leftrightarrow I$:
  - $\Diamond(A \to B),\Box(B \to A) \vdash \Diamond(A \leftrightarrow B)$
  - $\Box(A \to B),\Diamond(B \to A) \vdash \Diamond(A \leftrightarrow B)$
- $\Diamond \leftrightarrow E$:
  - $\Diamond(A \leftrightarrow B), \Box A \vdash \Diamond B$
  - $\Diamond(A \leftrightarrow B), \Box B \vdash \Diamond A$
  - $\Box(A \leftrightarrow B), \Diamond A \vdash \Diamond B$
  - $\Box(A \leftrightarrow B), \Diamond B \vdash \Diamond A$
- $\Box \bot I$:
  - $A, \neg A \vdash \Box \bot$
- $\Box \bot E$:
  - $\Box \bot \vdash \bot$
- $\Diamond \bot I$:
  - $A, \neg A \vdash \Diamond \bot$
- $\Diamond \bot E$:
  - $\Diamond \bot \vdash \bot$
- $\Box \neg I$:
  - $[\Diamond A \dots \bot] \vdash \Box \neg A$
- $\Box \forall I$:
  - $?$
- $\Box \forall E$:
  - $\Box \forall x A(x) \vdash \Box A(t/x)$
- $\Diamond \forall I$:
  - $?$
- $\Diamond \forall E$:
  - $\Diamond \forall x A(x) \vdash \Diamond A(t/x)$
- $\Box \exists I$:
  - $\Box A(t) \vdash \Box \exists x A(x/t)$
- $\Box \exists E$:
  - $\Box \exists x A(x),[\Box A(t/x) \dots \Box B] \vdash \Box B$
    - $t$ must be arbitrary and absent in $B$.
- $\Diamond \exists I$:
  - $\Diamond A(t) \vdash \Box \exists x A(x/t)$
- $\Diamond \exists E$:
  - $?$

### Supplemental Classical Modal Logic K (L+CK) Rules

- $\Diamond \neg I$:
  - $[\Box A \dots \bot] \vdash \Diamond \neg A$

### Modal Axiom D (L+IK+D) Rules

- $D$:
  - $\Box A \vdash \Diamond A$

### Modal Axiom M (L+IK+M) Rules

- $MI$:
  - $A \vdash \Diamond A$
- $ME$:
  - $\Box A \vdash A$

### Modal Axiom 4 (L+IK+4) Rules

- $4I$:
  - $\Box A \vdash \Box \Box A$
- $4E$:
  - $\Diamond \Diamond A \vdash \Diamond A$

### Modal Axiom B (L+IK+B) Rules

- $BI$:
  - $A \vdash \Box \Diamond A$
- $BE$:
  - $\Diamond \Box A \vdash A$
