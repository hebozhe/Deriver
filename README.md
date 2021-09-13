# Deriver

## Features

### Functionality

* Syntactic derivation for:
  * Propositional logic and
  * First-order logic.

### Work in Progress

* Syntactic derivation for:
  * Second-order logic,
  * Third-order logic,
  * Declarative logic, and
  * Modal logic.
  
## How-To Guide

Deriver accepts WFF's of a very specific form and produces derivations.

### Inputting Propositions

The inputs load right to left. So, for instance, if you have "A, B ⊢ C" as your sought derivation, you must enter "C" first.

If you enter only one proposition, Deriver will attempt to prove the proposition as a theorem.

### WFF's for Deriver

All propositions build upon each other, and logics can be mixed and matched.

* "⊥" is a WFF.
  * "⊤" is not a WFF.
* "φ", "ψ", and "χ" are propositional variables (variables encapsulating all second- and first-order propositions).
* "A" through "T" are predicate constants.
* "U" through "Z" are predicate variables.
* "a" through "t" are term constants.
* "u" through "z" are term variables.
* Any predicate constant following any number of constants is an atomic WFF.
  * Example: Propositions between "A" and "Abstraction" are all WFF's, but neither "U" nor "Au" are WFF's.
  * Parentheses around atomics are omitted.
* If "P" is a WFF, then "¬(P)" is a WFF (negation).
* If "P" and "Q" are WFF's, then "(P→Q)", "(P∧Q)", "(P∨Q)", and "(P↔Q)" are WFF's.
* If "P[c]" is a WFF with a term constant "c", then, if "x" is a variable, "∀x(P[x/c])" and "∃x(P[x/c])" are WFF's.
  * Variables can be recycled for scope.
  * Example: "∀x(Px∨∃xQx)" is a WFF. However, the outer "∀x", instantiated will not apply to any variables "x" within the scope of "∃x".
* If "P" is a WFF with a predicate constant "P", then, if "X" is a variable, "∀X(X)" and "∃X(X)" are WFF's.
  * The same scope rules as above apply.
* If "P" is a WFF, then "□(P)" and "◇(P)" are WFF's.
* If "P" is a WFF where "P" is at least a monadic predicate and "Q" is a WFF, then "P«Q»" is a WFF.
  * "«" and "»" are special string markers for quotation.
  * Example: "r says that j P's," can translate to "Sr«Pj»".
* If "P" is a WFF, then, if "φ" is a propositional variable, then "∀φ(φ)" and "∃φ(φ)" are WFF's.
  * Example: "All and only what a knight declares is true," can translate to, "∀x(∀φ(Dx«φ»→φ)↔Kx)".

***While Deriver can currently identify WFF's for all of these logics, it can only perform derivations for propositional and first-order logic as of this release.***

### Deriver's Rules of Inference

Deriver uses a elimination an introduction rule set similar to Gentzen's and a notation style similar Fitch's.

The rules are as follows:

Propositional rules:

| Operator | Elim Rule | Intro Rule |
| -------- | --------- | ---------- |
| ¬ | ¬¬P ⊢ P (¬E) | [P ... ⊥] ⊢ ¬P (¬I) |
| ⊥ | ⊥ ⊢ P (⊥E) | P, ¬P ⊢ ⊥ (⊥I) |
| → | P→Q, P ⊢ Q (→E) | [P ... Q] ⊢ P→Q (→I) |
| ∧ | P∧Q ⊢ P, Q (∧E) | P, Q ⊢ P∧Q (∧I) |
| ∨ | P∨Q, P→R, Q→R ⊢ R (∨E) | P ⊢ P∨Q, Q∨P (∨I) |
| ↔ | P↔Q ⊢ P→Q, Q→P (↔E) | P→Q, Q→P ⊢ P↔Q (↔I) |

First-order quantifier rules:

| Operator | Elim Rule | Intro Rule |
| -------- | --------- | ---------- |
| ∀ | ∀x(Px) ⊢ Pc (∀E)<br>for every "x" under the direct scope of "P" and for any constant "c" | [[c] ... Pc] ⊢ ∀x(Px) (∀I)<br>where "c" is an arbitrary constant |
| ∃ | ∃xPx, [Pc ... Q] ⊢ Q (∃E)<br>where "Pc" is an arbitary instantiation of "∃xPx" and "c" is not in "Q" | Pc ⊢ ∃x(Px) (∃I)<br>for at least one constant "c" |

Second-order quantifier rules: Forthcoming

Third-order quantifier rules: Forthcoming

Declarative rules: Forthcoming

Modal rules: Forthcoming (will only encapsulate axioms K, M, 4, and B)
