# Inference Rules for Natural Deduction

## Propositional Logic (PL)

With respect to propositional logic inference rules, every rule in a weaker logic is admissible in a stronger logic.

- TPL is weaker than PPL.
- PPL is weaker than MPL.
- MPL is weaker than IPL.
- IPL is weaker than CPL.

### Implicational Propositional Logic (TPL) Rules

- $\top I$:
  - $\vdash_{TPL} \top$
- $\to I$:
  - $[A \dots B] \vdash_{TPL} A \to B$
- $\to E$:
  - $A \to B, A \vdash_{TPL} B$

In Fitch-style proofs:

- $Reit$:
  - $A, [\dots] \vdash_{TPL} [\dots A]$

### Positive Propositional Logic (PPL) Rules

Where $A/B$ replaces predicate $B$ with predicate $A$:

- $\wedge I$:
  - $A, B \vdash_{PPL} A \wedge B$
- $\wedge E$:
  - $A \wedge B \vdash_{PPL} A$
  - $A \wedge B \vdash_{PPL} B$
- $\vee I$:
  - $A \vdash_{PPL} A \vee B$
  - $B \vdash_{PPL} A \vee B$
- $\vee E$:
  - $A \vee B, A \to C, B \to C \vdash_{PPL} C$
- $\leftrightarrow I$:
  - $A \to B, B \to A \vdash_{PPL} A \leftrightarrow B$
- $\leftrightarrow E$:
  - $A \leftrightarrow B \vdash_{PPL} A \to B$
  - $A \leftrightarrow B \vdash_{PPL} B \to A$
- $\top E$
  - $A, \Phi(A) \vdash_{PPL} \Phi(\top/A)$
    - **Caveat:** $A$ is not in a subformula of a $\Box$-formula or a $\Diamond$-formula.

### Minimal Propositional Logic (MPL) Rules

- $\bot I$:
  - $A, \neg A \vdash_{MPL} \bot$
- $\neg I$:
  - $[A \dots \bot] \vdash_{MPL} \neg A$

### Intuitionistic Propositional Logic (IPL) Rules

- $\bot E$:
  - $\bot \vdash_{IPL} A$

### Classical Propositional Logic (CPL) Rules

- $\neg E$:
  - $\neg \neg A \vdash_{CPL} A$

## N-ary Predicate Logic (NL)

### Implicational N-ary Predicate Logic with Identity (TNLi) Rules

- $=I$:
  - $\vdash_{TNLi} t=t$
- $=E$:
  - $t=t', A(t) \vdash_{TNLi} A(t'/t)$

## Quantificational Logic (QL)

Where $a/b$ replaces argument $b$ with argument $a$, and where $A/B$ replaces predicate $B$ with predicate $A$:

### Positive Quantificational Logic (PQL) Rules

- $\forall I$:
  - $[\top \dots A(t)] \vdash_{P1QL} \forall x A(x/t)$
    - **Caveat:** $t$ is fresh to the inner proof.
  - $[\top \dots \Phi(T)] \vdash_{P2QL} \forall X \Phi(X/T)$
    - **Caveat:** $T$ is fresh to the inner proof.
- $\forall E$:
  - $\forall x A(x) \vdash_{P1QL} A(t/x)$
  - $\forall X \Phi(X) \vdash_{P2QL} \Phi(A/X)$
- $\exists I$:
  - $A(t) \vdash_{P1QL} \exists x A(x/t)$
  - $\Phi(A) \vdash_{P2QL} \exists X \Phi(X/A)$
- $\exists E$:
  - $\exists x A(x), [A(t/x) \dots B] \vdash_{P1QL} B$
    - **Caveat:** $t$ is fresh to the inner proof and $B(\cancel{t})$.
  - $\exists X \Phi(X), [\Phi(T/X) \dots \Psi] \vdash_{P2QL} \Psi$
    - **Caveat:** $T$ is fresh to the inner proof and $\Psi(\cancel{T})$.

## Modal Logics

### Positive System K (PPL+K) Rules

- $\Box I(K)$:
  - $[\top \dots A] \vdash_{PPL+K} \Box A$
    - **Caveat:** $[\top \dots A]$ is an inner proof for $\Box I(K)$.
- $\Box E(K)$:
  - $\Box A, [\dots] \vdash_{PPL+K} [\dots A]$
    - **Caveat:** $[\dots]$ is an inner proof for $\Box I(K)$ or $\Diamond E(K)$.
- $\Diamond E(K)$:
  - $\Diamond A, [A \dots B] \vdash_{PPL+K} \Diamond B$
    - **Caveat:** $[A \dots B]$ is an inner proof for $\Diamond E(K)$.

### Minimal System K (MPL+K) Rules

- $\Box E(K)$:
  - $\neg \Diamond A, [\dots] \vdash_{MPL+K} [\dots \neg A]$
  - **Caveat:** $[\dots]$ is an inner proof for $\Box I(K)$ or $\Diamond E(K)$.
- $\Diamond E(K)$:
  - $\Diamond A, [A \dots \bot] \vdash_{MPL+K} \neg \Diamond A$
  - **Caveat:** $[A \dots \bot]$ is an inner proof for $\Diamond E(K)$.

### Classical System K (CPL+K) Rules

- $\Diamond I(K)$:
  - $\neg \Box A \vdash_{CPL+K} \Diamond \neg A$.

### Positive System D (PPL+D) Rules

- $\Box ED$:
  - $\Box A \vdash_{PPL+D} \Diamond A$

### Positive System M (PPL+M) Rules

- $\Diamond IM$:
  - $A \vdash_{PPL+M} \Diamond A$
- $\Box EM$:
  - $\Box A \vdash_{PPL+M} A$

### Positive System 4 (PPL+4) Rules

- $\Box I4$:
  - $\Box A \vdash_{PPL+4} \Box \Box A$
- $\Diamond E4$
  - $\Diamond \Diamond A \vdash_{PPL+4} \Diamond A$

### Positive System B (PPL+B) Rules

- $\Box IB$:
  - $A \vdash_{PPL+B} \Box \Diamond A$
- $\Diamond EB$:
  - $\Diamond \Box A \vdash_{PPL+B} A$
