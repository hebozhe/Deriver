# Inference Rules for Natural Deduction

## Propositional Logic (PL)

With respect to propositional logic inference rules, every rule in a weaker logic is admissible in a stronger logic.

- TPL is weaker than PPL.
- PPL is weaker than MPL.
- MPL is weaker than IPL.
- IPL is weaker than CPL.

### Implicational Propositional Logic (TPL) Rules

- $\top I$:
  - $\vdash \top$
- $\to I$:
  - $[A \dots B] \vdash A \to B$
- $\to E$:
  - $A \to B, A \vdash B$

### Positive Propositional Logic (PPL) Rules

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
  - $A \leftrightarrow B \vdash A \to B$
  - $A \leftrightarrow B \vdash B \to A$

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

## Quantificational Logic (QL)

Where $a/b$ replaces argument $b$ with argument $a$, and where $A/B$ replaces predicate $B$ with predicate $A$:

### Positive Quantificational Logic (PQL) Rules

- $\forall I$:
  - $[\top(t/x) \dots A(t)] \vdash \forall x A(x/t)$, where $t$ is arbitrary
  - $[\top(T/X) \dots \Phi(T)] \vdash \forall X \Phi(X/T)$, where $T$ is arbitrary
- $\forall E$:
  - $\forall x A(x) \vdash A(t/x)$
  - $\forall X \Phi(X) \vdash \Phi(A/X)$
- $\exists I$:
  - $A(t) \vdash \exists x A(x/t)$
  - $\Phi(A) \vdash \exists X \Phi(X/A)$
- $\exists E$:
  - $\exists x A(x),[A(t/x) \dots B(\xcancel{t})] \vdash B(\xcancel{t})$, where $t$ is arbitrary
  - $\exists X \Phi(X),[\Phi(T/X) \dots \Psi(\xcancel{T})] \vdash \Psi(\xcancel{T})$, where $T$ is arbitrary

## Quantificational Logic with Identity (QLi)

### Positive Quantificational Logic with Identity (PQLi) Rules

- $=I$:
  - $\vdash t=t$
- $=E$:
  - $t=t', A(t) \vdash A(t'/t)$

## System-Free Modal Logic

### Positive, System-Free Modal Logic Rules

- $\Box I$:
  - $[\top \dots A] \vdash \Box A$, where $[\top \dots A]$ is an inner proof for $\Box I$.
- $\Box E$:
  - $\Box A, [\dots] \vdash [\dots A]$, where $[\dots]$ is an inner proof for $\Box I$ or $\Diamond E$.
- $\Diamond E$:
  - $\Diamond A, [A \dots B] \vdash \Diamond B$, where $[A \dots B]$ is an inner proof for $\Diamond E$.

### Minimal, System-Free Modal Logic Rules

- $\Box E$:
  - $\neg \Diamond A, [\dots] \vdash [\dots \neg A]$, where $[\dots]$ is an inner proof for $\Box I$ or $\Diamond E$.
- $\Diamond E$:
  - $\Diamond A, [A \dots \bot] \vdash \neg \Diamond B$, where $[A \dots \bot]$ is an inner proof for $\Diamond E$.

### Classical, System-Free Modal Logic Rules

- $\Diamond I$:
  - $\neg \Box A \vdash \Diamond \neg A$.

## System-Bound Modal Logic

### Positive System K (L+K) Rules

- $\Box IK$:
  - $A \vdash \Box A$, when $\vdash A$, where $A$ is a non-modal formula

### Positive System KD (L+K+D) Rules

- $\Box ED$:
  - $\Box A \vdash \Diamond A$

### Positive System KM (L+K+M) Rules

- $\Diamond IM$:
  - $A \vdash \Diamond A$
- $\Box EM$:
  - $\Box A \vdash A$

### Positive System K4 (L+K+4) Rules

- $\Box I4$:
  - $\Box A \vdash \Box \Box A$
- $\Diamond E4$:
  - $\Diamond \Diamond A \vdash \Diamond A$

### Positive System KB (L+K+B) Rules

- $\Box IB$:
  - $A \vdash \Box \Diamond A$
- $\Diamond EB$:
  - $\Diamond \Box A \vdash A$
