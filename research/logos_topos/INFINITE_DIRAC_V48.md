# LTR v0.48: A norm-nuclear Dirac spectral-power family

**Date:** November 4, 2026  
**Target:** actual complex Hilbert space of the syntax-numbered nullary spectral triple.

## Verification receipts

The following theorems are imported into
[`Neoplatonic/LTR/Check.lean`](../../Neoplatonic/LTR/Check.lean)
and included in the audited dependency report.

- [LTR CI 41780811173](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41780811173)
  proves norm control, absolute summability of the genuine rank-two Hilbert
  operators, and equality of their operator-norm sum to the global
  spectral-power map.
- [LTR CI 41781213895](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41781213895)
  verifies the explicit finite-dimensional factorization certificate
  and the spectral-power semigroup law for arbitrary positive exponents.
- [LTR CI 41781897410](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41781897410)
  verifies the exponent-halving and squared-resolvent square-root identities.

Each cited run passed the Lean build, axiom audit, and finite
reconstruction test workflow on its corresponding source commit.

## The actual operator, not just its eigenvalue sequence

As previously proved, the maximal self-adjoint Dirac is built on
`H = ℓ²(ℕ, ℂ²)`. Its j-th two-dimensional block has

\[
D_j^2=(4^j+s_j^2)I_2,\qquad
R_j=(1+4^j+s_j^2)^{-1}I_2.
\]

For every real `p>0`, write

\[
w_{p,j}=(1+4^j+s_j^2)^{-p/2}>0,
\qquad A_p|_{H_j}=w_{p,j}I_2.
\]

The existing `chosenComplexSpectralPowerCLM` is a bounded complex-linear
operator on the **whole** Hilbert sum. The v0.47 trace theorem verified
the value of each standard-basis diagonal entry and its absolutely
summable global diagonal trace.

## New: convergent finite-rank decomposition in operator norm

[`ComplexSpectralNuclearSeries.lean`](../../Neoplatonic/LTR/ComplexSpectralNuclearSeries.lean)
defines a genuine finite-rank operator

\[
B_{p,j}=\iota_j\,(w_{p,j}I_2)\,\operatorname{ev}_j:
H\longrightarrow H,
\]

where `ev_j : H → ℂ²` and `ι_j : ℂ² → H` are the checked
continuous-linear evaluation and single-coordinate inclusion maps.

Lean proves that every `B_{p,j}` is compact, has range of dimension
at most two through its explicit factorization, and satisfies

\[
\|B_{p,j}\|\le w_{p,j}.
\]

Since the previously verified scalar comparison gives

\[
0\le w_{p,j}\le 2^{-jp},\quad p>0,
\]

the series of **actual operator norms** converges. Most importantly,
the kernel now verifies the equality in the Banach space of bounded
Hilbert operators:

\[
\boxed{A_p=\sum_{j=0}^{\infty}B_{p,j}}
\quad\text{(operator-norm convergence).}
\]

The result is stronger than convergence of partial block trace values.
It identifies the whole bounded operator as the norm-convergent sum of
its finite-rank pieces.

## Explicit formal nuclear certificate

[`ComplexSpectralRankTwoCertificate.lean`](../../Neoplatonic/LTR/ComplexSpectralRankTwoCertificate.lean)
defines `HasSummableRankTwoExpansion A` as a property requiring:

1. Each summand `B_j` to factor as `V_j ∘ U_j`, with
   `U_j : H → ℂ²` and `V_j : ℂ² → H`.
2. A convergent series `Σ_j ‖B_j‖`.
3. The operator equality `HasSum B A`, in the operator norm topology.

The theorem `chosenComplexSpectralPower_rankTwoCertificate`
constructs this certificate from the actual Hilbert coordinate maps
for **every** `p>0`.

By the standard finite-rank inequality `‖B_j‖₁ ≤ 2‖B_j‖`,
the certificate implies that `A_p` is trace class in the usual
Hilbert-space sense, with `Σ_j ‖B_j‖₁ < ∞`.
The `ℓ¹` operator sum and factorization are Lean-checked.

**Formalization boundary:** the general abstract trace-norm ideal,
the inequality `‖B_j‖₁ ≤ 2‖B_j‖` as a Lean theorem for arbitrary
rank-two Hilbert maps, and a bridge to an abstract Mathlib
`TraceClass` predicate remain outside the checked development.
The pinned Mathlib v4.35.0 contains finite-dimensional
`LinearMap.trace` machinery, which the existing block proofs use.
The current certificate is explicitly named and defined in this
repository to avoid presenting an unimplemented generic Schatten API
as verified.

For the present positive diagonal model, the mathematical trace is

\[
\operatorname{Tr}(A_p)=\|A_p\|_1
=2\sum_{j=0}^{\infty}(1+4^j+s_j^2)^{-p/2}
\le\frac{2}{1-2^{-p}}.
\]

The individual diagonal entries and their global summability and
value are Lean-checked in v0.47. The identity with a generic
trace-class trace functional remains a separate Lean theorem target.

## Positive spectral-power semigroup

[`ComplexSpectralPowerSemigroup.lean`](../../Neoplatonic/LTR/ComplexSpectralPowerSemigroup.lean)
proves strict positivity of the scalar squared-resolvent weights.
For all positive `p,q` the kernel proves the operator-level
semigroup identity

\[
\boxed{A_p\circ A_q=A_{p+q}.}
\]

Consequences also formalized and audited:

\[
A_p A_q=A_q A_p,\qquad
A_{p/2}^{,2}=A_p,\qquad
A_1^2=R=(I+D^2)^{-1}.
\]

The last identification uses the previously checked complex
maximal-domain, two-sided squared-resolvent inverse theorem.
These equalities hold in the actual infinite Hilbert algebra.

## Interpretive boundaries and next proof obligations

The family has the expected algebraic real-power laws, and every
weight is positive, but a full `cfc` identification of `A_p` with
the general functional-calculus power of the bounded positive
operator `R` has not yet been formalized. A proof of positivity of
the whole Hilbert operator and the uniqueness/continuity properties
of its positive real powers would close that bridge.

For the **unbounded** Dirac itself, deriving the same identification
through its spectral functional calculus would require additional
domain and spectral-measure packaging. Existing checked results
identify the p=2 resolvent and the complete semigroup of concrete
bounded diagonal powers.

The nonnegative `p`-summability threshold is zero because
the mass sequence `2^j` grows exponentially; this remains a
spectral property of the chosen Dirac marking. The Connes-style
dual metric previously recovered from its commutator depends
on the inverse-distance edge couplings. Exact dimension comparisons
with the completed-theory Stone metric are distinct mathematical
questions.

The logical sentence encoder is constructive, while the dense
sequence of completed theories used to mark the Dirac remains
classically selected.

## Reproduce

```sh
lake build Neoplatonic.LTR.Check
lake env lean Neoplatonic/LTR/Check.lean
python3 -m unittest discover -s research/logos_topos -p 'test_*.py' -v
```
