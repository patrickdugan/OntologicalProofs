# LTR v0.46: Concrete logical Dirac and exact spectral metric recovery

**Date:** November 4, 2026

## Verification ledger

The following theorem modules are committed directly to main,
included in `Neoplatonic/LTR/Check.lean`, and checked by the
project's Lean kernel build, explicit axiom audit and finite tests.

- [v0.43 concrete Hilbert Boolean operators and syntactic pullback, run 41765765066](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41765765066)
- [v0.44 direct indexed Lipschitz and marked commutator bounds, run 41766135627](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41766135627)
- [v0.45 selected concrete Dirac marking and constructor equality, run 41766537302](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41766537302)
- [v0.46 concrete spectral metric recovery, run 41766876738](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41766876738)

The corresponding source files are

- [`NullaryEffectiveOperatorPullback.lean`](../../Neoplatonic/LTR/NullaryEffectiveOperatorPullback.lean)
- [`NullaryEffectiveQuantitativeOperators.lean`](../../Neoplatonic/LTR/NullaryEffectiveQuantitativeOperators.lean)
- [`NullaryEffectiveMarkedTriple.lean`](../../Neoplatonic/LTR/NullaryEffectiveMarkedTriple.lean)
- [`NullaryEffectiveMetricRecovery.lean`](../../Neoplatonic/LTR/NullaryEffectiveMetricRecovery.lean).

The preceding [LTR v0.42 ledger](INFINITE_DIRAC_V42.md) details
the constructive sentence-code round-trip, the direct program-index
lookup, and the construction of the concrete nullary spectral triple.

## The concrete first-order spectral geometry

Let `L` be the actual nullary first-order language consisting of
countably many independent zero-arity relation symbols. Let `T`
be the single-axiom theory whose models have at most one element.

Mathlib's genuine space of complete expanded-language theories is

\[
X=T.\operatorname{CompleteType}(\mathrm{Empty}).
\]

The now-verified constructive `Encodable` interface produces
a total surjective natural-number sentence numbering

\[
c:\mathbb N\twoheadrightarrow
\operatorname{Sentence}(L[[\mathrm{Empty}]]).
\]

For completions \(p,q\), the metric is the dyadic first-disagreement
metric \(d_c\), built from their Boolean truth values at numbered
sentences. This metric induces the actual Stone topology.

The concrete spectral triple consists of

\[
A_0=\operatorname{Lip}(X,\mathbb C),
\qquad H=\ell^2(\mathbb N,\mathbb C^2),
\]

with the faithful diagonal representation of the continuous
complex function algebra. The maximal-domain Dirac has blocks

\[
D_j=
\begin{pmatrix}
2^j& d_c(x_j,y_j)^{-1}\\
d_c(x_j,y_j)^{-1}& -2^j
\end{pmatrix}
\]

for the classically chosen dense-pair marked endpoints
\(x_j,y_j\). All edges are nondegenerate. The operator is
self-adjoint, with compact ordinary resolvent; each element
of \(A_0\) has a bounded commutator and preserves its domain.

## Hilbert Boolean algebra and full syntactic translation

For any first-order expanded sentence \(\varphi\), let
\(p_\varphi:X\to\{0,1\}\subset\mathbb C\) be its truth projection,
and let \(P_\varphi=\pi(p_\varphi)\).

The Lean theorems in v0.43 verify

\[
P_{\neg\varphi}=I-P_\varphi,\qquad
P_{\varphi\land\psi}=P_\varphi P_\psi,
\]

as identities in the specific infinite-dimensional Hilbert
operator algebra of the one-axiom theory.

An actual partial-recursive program \(e\) defines the
first-order language endomorphism \(\sigma_e\) and corresponding
continuous complete-type map \(F_e:X\to X\).

The full-sentence projection pullback is

\[
\boxed{\pi(p_\varphi\circ F_e)
       =\pi(p_{\sigma_e(\varphi)}).}
\]

The named pulled-back projection is admissible in the concrete
Lipschitz algebra and has a bounded maximal-domain Dirac
commutator. These are actual represented Hilbert operators.

For the \(j\)th numbered sentence, the direct encoded syntactic
lookup satisfies \(c(k_e(j))=\sigma_e(c(j))\). V0.44 proves

\[
\boxed{
\operatorname{Lip}(p_{c(j)}\circ F_e)\le2^{k_e(j)}
}
\]

and the corresponding numerical bound on the genuine
bounded marked-edge Hilbert commutator

\[
\boxed{
\|[D,\pi(p_{c(j)}\circ F_e)]\|\le2^{k_e(j)}
}
\]

for every nondegenerate edge marking and arbitrary diagonal
mass sequence, including the form used by this spectral triple.

The finite upper bound is determined by the syntactic index,
and may be very large. It does not provide a uniform finite
global Lipschitz constant for \(F_e\).

## The selected complete-type marking

V0.45 introduces explicit Lean names for the chosen
topologically dense sequence \(\{q_n\}\) of actual complete types,
the two fallback indices selected from an independent sentence,
and the marked left and right endpoints.

Lean verifies that all marked endpoints are distinct, that
every \(q_n\) occurs among them, and that for every ordered pair
\(q_m\ne q_n\), some marked block has endpoints \((q_m,q_n)\).

The theorem
`effectiveNullaryStoneSpectralTriple_eq_explicit` verifies
that the v0.41 concrete spectral-triple record equals this
named dense-pair construction.

## Exact Connes-style dual metric recovery

The main v0.46 theorem is

`effectiveNullaryStoneSpectralTriple_metric_recovery`.

For any completions \(p,q\in X\), it proves an upper-bound
statement for every admissible \(f\in A_0\) with a
bounded infinite-dimensional Dirac commutator of norm at most 1:

\[
\|f(p)-f(q)\|\le d_c(p,q).
\]

It also constructs an admissible \(f\) with a certified
commutator norm at most 1 for which equality holds:

\[
\|f(p)-f(q)\|=d_c(p,q).
\]

Together these two kernel-checked statements yield the
mathematical equivalent of the Connes-style dual formula

\[
\boxed{
d_c(p,q)=
\sup_{\substack{f\in A_0\\\|[D,\pi(f)]\|\le1}}
\|f(p)-f(q)\|.
}
\]

The Lean theorem formalizes the upper bound and an
attaining witness rather than a separate use of a real
`sSup` operator. The commutators are actual bounded
Hilbert extensions of those defined on the maximal
unbounded Dirac domain.

This goes beyond a formal statement about a generic
metric space: the theorem specializes the recovered
metric, representation, observable algebra and marked
Dirac to the actual syntax-numbered nullary theory.

## Remaining mathematical and effective obligations

The syntax encoder, decoder, and program-index lookup are
constructive Lean definitions. Mathlib's formal
`Primrec`/`Computable` classification for substitutions
on full first-order syntax is a distinct task.

The dense complete-type sequence and marked Hilbert
blocks are selected classically. An effective way of
obtaining those exact complete theories is still open
under the appropriate oracle assumptions.

The scalar spectral-energy series converges for all
positive real exponents in the previous formalization.
A global Hilbert operator trace identity, trace-class
packaging and resulting spectral-dimension theorem
remain to be proved.

The exact logical projection pullback is a statement
in the represented observable algebra. It does not
produce a unitary Dirac intertwiner for arbitrary
interpretations or make metric distortion uniform
across all Lipschitz observables.

## Reproduce

```shell
lake build Neoplatonic.LTR.Check
lake env lean Neoplatonic/LTR/Check.lean
python3 -m unittest discover -s research/logos_topos -p 'test_*.py' -v
```
