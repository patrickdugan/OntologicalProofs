# LTR v0.31: A sentence-numbered ultrametric spectral triple

**Date:** November 4, 2026

## Verified Lean milestones

- [v0.28 first-disagreement metric, run 41754732444](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41754732444)
- [v0.29 numbered Stone spectral triple, run 41755196287](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41755196287)
- [v0.30 quantitative sentence-commutator bound, run 41755908445](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41755908445)
- [v0.31 ultrametric and finite-prefix balls, run 41756584189](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41756584189)

All of these ran the Lean build, printed kernel axiom dependencies and
passed the project's axiom and finite reconstruction tests.

## The numbered logical metric

Let `L` be a first-order language, `T` a theory, and `α` a type
of variables. Let

\[
X=T.\operatorname{CompleteType}(\alpha)
\]

be Mathlib's genuine Stone space of complete types, and fix a
surjective numbering

\[
c:\mathbb N\twoheadrightarrow (L.\operatorname{withConstants}(\alpha)).\operatorname{Sentence}.
\]

This is a mathematical numbering, supplied as an argument. Define

\[
b_p(n)=
\begin{cases}
1,&c(n)\in p,\\
0,&c(n)\notin p.
\end{cases}
\]

The map `p ↦ b_p` into \(\mathbb N\to\mathrm{Bool}\) is continuous,
as every coordinate is the indicator of a clopen sentence locus.
Surjectivity of `c` makes it injective. The source is compact
and the target Hausdorff, so the truth-sequence map is an embedding.

Using Mathlib's `PiNat.metricSpace`, pull back the first-disagreement
distance along that embedding. For distinct `p,q`, set

\[
N_c(p,q)=\min\{n:c(n)\in p\ \Leftrightarrow\ c(n)\notin q\}.
\]

Then the constructed metric is

\[
\boxed{
d_c(p,q)=
\begin{cases}
0,&p=q,\\
2^{-N_c(p,q)},&p\ne q.
\end{cases}}
\]

`numberedSentenceMetric` preserves the existing complete-type
Stone topology by Mathlib's embedding-metric construction. The
`numberedSentenceMetric_firstDisagreement` theorem verifies
the displayed formula directly.

## Non-Archimedean geometry and finite logical information

Lean proves

\[
d_c(p,r)\le\max\{d_c(p,q),d_c(q,r)\}.
\]

The sharper finite-prefix theorem states

\[
\boxed{
d_c(p,q)\le2^{-n}
\quad\Longleftrightarrow\quad
\forall i<n,\ (c(i)\in p\iff c(i)\in q).
}
\]

Thus each closed radius-\(2^{-n}\) ball is exactly a class of
completions agreeing on a finite initial fragment of the selected
sentence enumeration.

## Numbered spectral triple

If the expanded-language sentence type is countable, `T` is
satisfiable, and some sentence is independent of `T`, the
`numberedLogicalStoneSpectralTriple` constructor uses the metric
`d_c`, a classically selected dense sequence of genuine complete
theories, and the verified `Nat.unpair` edge marking.

The constructed data are

\[
\begin{aligned}
A&=C(X,\mathbb C),\\
A_0&=\operatorname{Lip}(X,\mathbb C),\\
H&=\ell^2(\mathbb N,\mathbb C^2),\\
\pi(f)_j&=\operatorname{diag}(f(x_j),f(y_j)),\\
D_j&=\begin{pmatrix}
2^j&d_c(x_j,y_j)^{-1}\\
d_c(x_j,y_j)^{-1}&-2^j
\end{pmatrix}.
\end{aligned}
\]

The earlier Lean-verified constructor establishes a faithful
star-algebra representation, dense Lipschitz subalgebra,
densely defined self-adjoint Dirac operator, compact ordinary
resolvent and bounded commutators on `A_0`. The all-dense-pairs
marking satisfies the hypotheses of the verified Connes-style
exact metric-recovery theorem for the newly chosen `d_c`.

For a countable sentence type, `classicalSentenceNumbering`
also selects a surjective numbering; this depends on classical
choice and does not claim a computable enumeration.

## Quantitative sentence commutators

Let `P_n` be the complex truth projection of sentence `c(n)`.
A change in the `n`th truth coordinate requires distance
at least `2^(-n)`, so Lean proves

\[
\boxed{\operatorname{Lip}(P_n)\le2^n.}
\]

Using the previously verified exact two-point commutator
formula and the reciprocal-distance edge scaling, the
`numberedSentenceProjection_commutator_norm_le` theorem proves

\[
\boxed{\|[D,\pi(P_n)]\|\le2^n}
\]

for the bounded Hilbert commutator extending the maximal-domain
unbounded commutator, uniformly over every nondegenerate marked
edge sequence and arbitrary real Dirac masses.

The bound is sensitive to which numbered sentence is under
consideration. It depends on the chosen presentation.

## Effective and spectral limitations

The construction is explicit *relative to* a surjective sentence
numbering, while computing a completion's Boolean truth sequence
may be undecidable. Even a computable enumeration of sentence
syntax does not supply a computable complete theory or a distance
algorithm for arbitrary completion points.

A different sentence numbering can change the metric scale
and quantitative bounds while preserving the underlying Stone
topology. No interpretation-natural metric or Dirac intertwiner
is asserted for arbitrary syntactic translations.

The scalar spectral energy series is verified summable for
every positive real exponent. A global operator trace identity
and Schatten-class formalization remain open, so a formally
verified spectral dimension has not yet been packaged.

## Proof files

- [NumberedSentenceMetric.lean](../../Neoplatonic/LTR/NumberedSentenceMetric.lean)
- [NumberedStoneSpectralTriple.lean](../../Neoplatonic/LTR/NumberedStoneSpectralTriple.lean)
- [NumberedSentenceLipschitz.lean](../../Neoplatonic/LTR/NumberedSentenceLipschitz.lean)
- [NumberedSentenceUltrametric.lean](../../Neoplatonic/LTR/NumberedSentenceUltrametric.lean)
- [NumberedSentenceFinitePrefix.lean](../../Neoplatonic/LTR/NumberedSentenceFinitePrefix.lean)

## Reproduce

```shell
lake build Neoplatonic.LTR.Check
lake env lean Neoplatonic/LTR/Check.lean
python3 -m unittest discover -s research/logos_topos -p 'test_*.py' -v
```
