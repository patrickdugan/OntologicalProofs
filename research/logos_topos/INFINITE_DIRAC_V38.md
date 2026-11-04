# LTR v0.38: Concrete nullary-language interpretation moduli

**Date:** November 4, 2026

## Verification record

Four successive Lean builds passed, with explicit kernel axiom reports
and finite reconstruction regression tests.

- [v0.35 full expanded sentence semantics, run 41760891885](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41760891885)
- [v0.36 concrete sentence-numbered modulus, run 41761181905](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41761181905)
- [v0.37 full nullary signature countability and fixed numbering, run 41761588153](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41761588153)
- [v0.38 two-program composition, run 41761968894](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41761968894)

The implementation modules are:

- [NullaryFullSentenceTranslation.lean](../../Neoplatonic/LTR/NullaryFullSentenceTranslation.lean)
- [NullaryConcreteNumberedModulus.lean](../../Neoplatonic/LTR/NullaryConcreteNumberedModulus.lean)
- [NullaryCountableSyntaxMetric.lean](../../Neoplatonic/LTR/NullaryCountableSyntaxMetric.lean)
- [NullaryProgramComposition.lean](../../Neoplatonic/LTR/NullaryProgramComposition.lean)

## The concrete first-order language

The existing Nullary.L has no function symbols. Its only relation
symbols are the independent nullary predicates P_n indexed by ℕ.
The theory Nullary.T has one nonlogical axiom: the domain contains
at most one element.

Earlier modules prove that all complete types of this theory with
an empty variable-constant expansion correspond bijectively, and
homeomorphically, to Boolean streams.

For any partial-recursive program code e, Nullary.haltingRename e
is a genuine Mathlib language homomorphism, and Nullary.syntaxMap e
is the induced endomorphism of actual complete first-order theories.
The function on stream coordinates reads n or 2n according to the
bounded halting signal computed at stage n.

The previous semantic theorem already covered all original-language
sentences, including quantifiers, but the v0.34 metric theorem
takes a surjective numbering of all *expanded-language* sentences.
This release provides the exact bridge.

## An equivalence of full sentence types

Mathlib provides the language equivalence

\[
E:\mathrm{Nullary.L}\ \simeq_L\
     \mathrm{Nullary.L}[[\mathrm{Empty}]]
\]

using FirstOrder.Language.LEquiv.addEmptyConstants.
Its sentence equivalence is

\[
E_*:\mathrm{Sentence}(\mathrm{L})
 \simeq\mathrm{Sentence}(\mathrm{L}[[\mathrm{Empty}]]).
\]

The Lean theorem emptyConstantSentenceEquiv_apply proves that E_*
is exactly the earlier liftedSentence operation.
The inverse unliftExpandedSentence is proved two-sided.

For any expanded sentence ψ, define

\[
\sigma_e(\psi)=
 E_*\bigl(\mathrm{haltingRename}(e)
      (\ E_*^{-1}(\psi)\ )\bigr).
\]

The theorem syntaxMap_expanded_semantics proves, for every
completion p and *every* expanded first-order sentence ψ,

\[
\boxed{
\psi\in F_e(p)\quad\Longleftrightarrow\quad
\sigma_e(\psi)\in p.
}
\]

The result includes quantified sentences and requires no external
semantic-pullback assumption.

## Actual full-sentence indexing and continuity

The full nullary language symbol type is proved countable: functions
are empty at every arity, relations are ℕ at arity zero and empty
elsewhere. Mathlib's first-order formula encoding then proves
Countable L[[Empty]].Sentence.

The module NullaryCountableSyntaxMetric installs that instance
and constructs a fixed classical surjective enumeration

\[
c:\mathbb N\twoheadrightarrow
 \mathrm{Sentence}(\mathrm{L}[[\mathrm{Empty}]]).
\]

For every program e, the index lookup k_e is chosen so that

\[
\boxed{c(k_e(j))=\sigma_e(c(j)).}
\]

By the preceding semantic theorem, the required truth-pullback law is

\[
c(j)\in F_e(p)\iff c(k_e(j))\in p.
\]

With the finite-prefix modulus introduced in v0.32,

\[
M_e(n)=
\max\bigl(\{k_e(j)+1:j<n\}\cup\{0\}\bigr),
\]

the actual program-induced complete-type map satisfies

\[
\boxed{
d_c(p,q)\le2^{-M_e(n)}
\implies
d_c(F_e(p),F_e(q))\le2^{-n}.
}
\]

The theorem nullaryProgram_numbered_uniformModulus additionally proves
the epsilon-delta form of uniform continuity on this fixed
sentence-numbered Stone metric. For every ε>0, choosing n with
2^(-n)<ε and δ=2^(-M_e(n)) provides a valid modulus.

The fixed code is obtained by classical choice, and the lookup uses
Classical.choose applied to surjectivity. The result specifies a
mathematical finite bound for each chosen lookup. It does not assert
computability of this lookup or membership in arbitrary complete types.

## Genuine program composition

The theorem syntaxMap_comp_expanded_semantics verifies the exact
semantics for two codes e and f:

\[
\boxed{
\psi\in F_f(F_e(p))
\iff
\sigma_e(\sigma_f(\psi))\in p.
}
\]

The inverse order of syntactic substitutions is the correct
contravariant order for pullback on completed theories.

The full-sentence lookup for the composition is k_e ∘ k_f.
Lean verifies that it correctly translates each enumerated
sentence and that agreement of source completions through
M_e(M_f(n)) forces target agreement through n.

The v0.38 metric theorem states

\[
\boxed{
d_c(p,q)\le 2^{-M_e(M_f(n))}
\implies
d_c(F_f(F_e(p)),F_f(F_e(q)))\le2^{-n}.
}
\]

This is an instantiated composition result for the actual
partial-recursive nullary-language maps. The general v0.34
proof provided the composition machinery; the semantic
hypotheses are discharged by the concrete verified model theory.

## Scope and remaining obligations

The work uses true first-order sentences, complete-type Stone
spaces, and a mathematically concrete sequence of partial-recursive
language renamings. It is stronger than a Boolean-stream toy example
because the syntactic map and its quantified semantics are verified.

The program-code-to-stream-coordinate transformation is defined by
bounded evaluation, but the fixed full-sentence enumeration is
classically chosen. A computable decoder/encoder for all sentences,
and a computable surjective numbering with an effective index lookup,
remain tasks for a genuinely effective moduli theorem.

Uniform continuity in these metrics is compatible with the earlier
kernel-verified undecidability of finite Lipschitz regularity
for the atom-coordinate metric. Topological continuity and a finite
global Lipschitz constant are different mathematical properties;
reindexing changes quantitative scales.

The numbered spectral triple from v0.29 supplies a self-adjoint
Dirac, compact ordinary resolvent and faithful operator algebra.
This release proves concrete semantic and metric maps between its
completion-space presentations. It does not construct a unitary
intertwiner carrying one Dirac operator to another or an explicit
Schatten trace-class operator identity.

## Reproduce

    lake build Neoplatonic.LTR.Check
    lake env lean Neoplatonic/LTR/Check.lean
    python3 -m unittest discover -s research/logos_topos -p 'test_*.py' -v
