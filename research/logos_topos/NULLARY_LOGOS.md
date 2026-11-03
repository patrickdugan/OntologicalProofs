# LTR-04b: A one-axiom first-order realization of Cantor-stream geometry

## Mathematical construction

Let \(L\) be the countable first-order language whose only nonlogical
symbols are nullary predicates \(P_n\), indexed by \(n\in\mathbb N\).
There are no function symbols and no positive-arity relation symbols.

Take the single-axiom theory

\[
T=\{\neg\exists x\exists y\, (x\ne y)\}.
\]

The logic uses nonempty first-order structures, so every model of \(T\)
has exactly one element. In Lean, the axiom is the negation of
`FirstOrder.Language.Sentence.cardGe L 2` and its finiteness is proved
by `Nullary.finite_axioms`.

Given \(b:\mathbb N\to\{0,1\}\), let \(M_b\) be the one-element
structure in which \(P_n\) is true exactly when \(b(n)=1\).
The concrete Lean structure `Nullary.unitStructure b` satisfies the
axiom and proves

\[
M_b\models P_n\iff b(n)=1.
\]

The code also constructs the genuine mathlib complete type
\(\operatorname{encode}(b): T.\mathrm{CompleteType}(\varnothing)\)
through `T.typeOf`.

### Semantic independence

Both truth values of \(P_n\) occur in models of \(T\), independently
for every \(n\). The checked results

- `Nullary.not_entails_atom`
- `Nullary.not_entails_not_atom`
- `Nullary.independent_atom`

prove \(T\not\models P_n\) and \(T\not\models\neg P_n\).
The explicit model construction gives more: every infinite Boolean
assignment is realized simultaneously by a one-element model.

### Genuine syntactic endomorphisms

For each function \(\sigma:\mathbb N\to\mathbb N\), the code builds
`Nullary.rename σ : L →ᴸ L`, a mathlib first-order language
homomorphism. It acts on all first-order formulas and sentences through
the existing `LHom.onFormula` and `LHom.onSentence` operations, and
the checked atomic identity is

\[
\sigma_*(P_n)=P_{\sigma(n)}.
\]

This is actual syntactic substitution within the declared language.

For a partial-recursive code \(e\), write \(H_e(n)\) for the Boolean
question whether the fuel-bounded universal evaluator has halted by
stage \(n\). The induced syntax map uses

\[
\sigma_e(n)=
\begin{cases}
2n & H_e(n),\\
n & \neg H_e(n).
\end{cases}
\]

`Nullary.haltingRename` is the language endomorphism with this index.
The kernel-checked atomic realization theorem states

\[
M_b\models \sigma_{e*}(P_n)
\quad\Longleftrightarrow\quad
F_e(b)(n)=1.
\]

The map \(F_e\) is the total Cantor-space transformation developed
in `HaltingGeometry.lean`: after activation its \(n\)-th output bit
reads the \(2n\)-th input bit, and otherwise it reads the \(n\)-th
input bit. This gives a concrete syntax-to-stream bridge.

## Gödelian connection

The previously checked Lean theorem
`finite_real_lipschitz_undecidable` proves that no algorithm
uniformly decides whether these total computable Cantor-space maps
have a finite Lipschitz constant. It reduces that decision to
mathlib's actual partial-recursive halting theorem.

A noteworthy distinction: this is **not** an incompleteness theorem
for the one-axiom theory itself. The undecidable predicate is a
meta-level regularity property of a recursively presented family
of *endomorphisms*. The mathematical relationship is between
computability of syntactic translations and bounded geometric
distortion in an effectively marked completion space.

The derived spectral corollary uses the established identity
\(L_D(a)=\|[D,\pi(a)]\|=\operatorname{Lip}(a)\) in a separately
constructed spectral realization. The Lean kernel formalizes
the metric/observable statements; the unbounded operator-domain
construction is a written analytic proof.

## Completion-space status

`Nullary.encode` maps every Boolean stream into an actual first-order
complete type. `NullaryTypes.lean` now kernel-checks the membership
correspondence with lifted atomic sentences, the round-trip
\(\mathrm{decode}\circ\mathrm{encode}=\mathrm{id}\), and injectivity.
The complete-type injection passed GitHub Actions run 41559495766.
`NullarySemantics.lean` separately attempts to prove the all-sentence
semantic action using reducts; check its CI status before treating that
additional theorem as verified.

A complete homeomorphism with Cantor space would also require
surjectivity and continuity of the coordinate correspondence.
The expected mathematical proof uses quantifier elimination over
single-element models: every first-order sentence is equivalent
modulo \(T\) to a Boolean combination of finitely many nullary
atoms. Formalizing that normalization is an open integration task.

The same issue arises for a fully explicit semantic action of a
syntax map on *all* complete types. The present syntax theorem
acts on all formulas and verifies its model-level effect on every
atomic coordinate. A full functor on completion spaces can follow
from the normalization theorem.

## Proof ledger

| Claim | Status |
|---|---|
| One nonlogical axiom, countably many nullary symbols | Lean |
| Every Boolean stream has an explicit singleton model | Lean |
| Every nullary atom is independent of the theory | Lean |
| Actual `LHom` maps atoms by arbitrary index reassignments | Lean |
| Halting-index endomorphisms reproduce the Cantor map on atoms | Lean |
| Halting-hardness of finite Lipschitz bounds | Lean, Mathlib halting theorem |
| Bit recovery from `CompleteType`, injectivity | Lean, CI run 41559495766 |
| Full-sentence semantics via language reduct | Submitted in NullarySemantics; verify CI |
| Full complete-type Cantor homeomorphism | Written route, Lean open |
| Infinite-dimensional spectral operator analysis | Written proof, Lean open |

This file is a mathematical note. It contains no theological
predicates or conclusions.
