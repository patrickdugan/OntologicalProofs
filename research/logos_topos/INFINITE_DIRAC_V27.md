# LTR v0.27: Boolean Hilbert projections, syntactic pullback and an effective norm gap

**Date:** November 4, 2026

## Lean verification

The dedicated LTR Reconstruction workflow built the proof dependencies,
printed the kernel axiom report, checked it for `sorryAx` and native
reduction axioms, and ran the finite regression tests.

- [v0.24 Boolean operator audit, run 41750498830](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41750498830)
- [v0.25 syntactic Hilbert pullback audit, run 41751175180](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41751175180)
- [v0.26 Hilbert norm computability audit, run 41751595209](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41751595209)
- [v0.27 C*-norm-gap audit, run 41752172510](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41752172510)

The implementation resides in:

- [`LogicalBooleanOperators.lean`](../../Neoplatonic/LTR/LogicalBooleanOperators.lean)
- [`LogicalSyntacticHilbertPullback.lean`](../../Neoplatonic/LTR/LogicalSyntacticHilbertPullback.lean)
- [`LogicalHilbertUndecidability.lean`](../../Neoplatonic/LTR/LogicalHilbertUndecidability.lean)
- [`LogicalHilbertNormGap.lean`](../../Neoplatonic/LTR/LogicalHilbertNormGap.lean)

## Setup and standing assumptions

Let \(T\) be a satisfiable first-order theory whose expanded sentence
type is countable. Assume there is an independent sentence \(\eta\).
The earlier verified logical Stone spectral triple constructs a
classically selected metric on the genuine complete-type space

\[
X=T.\operatorname{CompleteType}(\alpha),
\]

a dense sequence of actual complete types, and an all-dense-pairs
marked Dirac operator on

\[
H=\ell^2(\mathbb N,\mathbb C^2).
\]

The representation
\(\pi:C(X,\mathbb C)\to\mathcal B(H)\) is faithful and
star-preserving. The admissible star subalgebra
\(\operatorname{Lip}(X,\mathbb C)\) is dense in \(C(X,\mathbb C)\);
its observables have bounded unbounded-domain Dirac commutators.

For each sentence \(\varphi\), set
\(U_\varphi=\{p\in X:\varphi\in p\}\),
\(p_\varphi=1_{U_\varphi}\) and \(P_\varphi=\pi(p_\varphi)\).

## Boolean algebra on the infinite Hilbert space

The verified `LogicalBooleanOperators` results give

\[
\boxed{P_{\neg\varphi}=I-P_\varphi,\qquad
P_{\varphi\land\psi}=P_\varphi P_\psi.}
\]

They also show

\[
\boxed{
P_\varphi=P_\psi \iff U_\varphi=U_\psi,
\qquad
P_\varphi P_\psi=P_\varphi \iff U_\varphi\subseteq U_\psi.
}
\]

Thus a sentence's semantic content as a clopen truth locus is
faithfully retained in the algebraic relations of genuine bounded
operators. Equality of sentence *syntax* is stronger than equality
of these projections; different sentences may define the same
truth locus modulo \(T\).

## Syntactic translation of logical projections

For the explicit one-axiom nullary-language construction, let
\(F_e:X\to X\) be the continuous complete-type map associated
with a partial-recursive code \(e\), and let \(\sigma_e\) be its
verified syntactic sentence translation.

Lean proves that complex truth projections satisfy

\[
p_\varphi\circ F_e=p_{\sigma_e(\varphi)}
\quad\Longrightarrow\quad
\boxed{\pi(p_\varphi\circ F_e)=P_{\sigma_e(\varphi)}}.
\]

The pullback of every such sentence projection is again in the
dense Lipschitz algebra of the chosen metric, so it preserves
the maximal Dirac domain and admits a bounded commutator.

This naturality applies to the *labelled observables*. The code
does not construct a unitary or other Dirac-intertwining operator
for \(F_e\). A continuous syntactic map may have unbounded
global Lipschitz distortion.

## Hilbert norm gap and effective obstruction

The earlier refutation result states
\(\|P_{\neg\varphi}\|=0 \iff T\models\varphi\).
The new v0.27 theorem uses the C*-identity and the
self-adjoint idempotence of \(P_\varphi\) to prove

\[
\|P_\varphi\|\in\{0,1\}.
\]

Consequently the refutation operator has an *exact* gap:

\[
\boxed{
\|P_{\neg\varphi}\|=
\begin{cases}
0 & T\models\varphi,\\
1 & T\not\models\varphi.
\end{cases}
}
\]

For a natural-number sentence numbering \(n\mapsto\varphi_n\),
Lean proves

\[
\operatorname{ComputablePred}
(n\mapsto\|P_{\neg\varphi_n}\|=0)
\iff
\operatorname{ComputablePred}
(n\mapsto T\models\varphi_n).
\]

A separate theorem shows that, for any estimate \(r\in\mathbb R\),

\[
|r-\|P_{\neg\varphi}\||<\tfrac12
\quad\Longrightarrow\quad
\bigl(r<\tfrac12\iff T\models\varphi\bigr).
\]

With an explicit premise that entailment for the chosen code is
undecidable, there cannot exist a uniformly half-accurate
estimator whose half-threshold predicate is computable.
The premise concerning the threshold is stated in Lean;
the theorem does not silently presume an effective
representation for arbitrary real outputs.

These are exact consequences of logical semantics and
the C*-algebraic structure. Their novelty is the verified
connection to the constructed infinite-Hilbert Dirac triple.
The classical theorem that specific arithmetic theories have
undecidable entailment is still an external input.

## Remaining mathematical work

The metric and dense complete-type sequence are currently chosen
by classical existence arguments. A presentation-sensitive metric
defined directly from a concrete sentence enumeration would
advance the effective construction.

Preservation of labelled projections under syntactic pullback
does not establish preservation of the Dirac operator or
commutator seminorm under arbitrary interpretations; that
requires a controlled metric/distortion hypothesis.

The scalar spectral-energy sum converges for all \(p>0\).
A formal trace identity and Schatten-class proof remain
separate obligations before claiming a verified spectral
dimension. No conclusion in this ledger depends on a
theological interpretation of the formalism.

## Reproduce

```shell
lake build Neoplatonic.LTR.Check
lake env lean Neoplatonic/LTR/Check.lean
python3 -m unittest discover -s research/logos_topos -p 'test_*.py' -v
```
