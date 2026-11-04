# LTR v0.47: Global spectral power trace, in progress

**November 4, 2026.**

## Verified starting point

LTR v0.46 gives an explicit syntax-numbered complex Dirac spectral triple
on `H = ℓ²(ℕ, ℂ²)`, with exact metric recovery, classical dense-pair
marking, and a concrete maximum-domain self-adjoint Dirac. The earlier
`ComplexSpectralSummability.lean` proves the scalar series
`Σ_j 2(1+4^j+s_j²)^(-p/2)` summable for every `p > 0`.
The initial spectral-power operator and its two-dimensional block
trace passed workflow 41774594301.

## New formal statements

The module
[`ComplexSpectralGlobalTrace.lean`](../../Neoplatonic/LTR/ComplexSpectralGlobalTrace.lean)
constructs:

- `complexSingleSpectralPowerBlock`: the genuine Hilbert-space map
  with image supported in the j-th copy of ℂ²;
- `finiteComplexSpectralPower`: its first-N-block truncation;
- `finiteComplexSpectralPower_apply`: exact coordinatewise action
  with weights `w_p(j) = (1+4^j+s_j²)^(-p/2)`;
- `finiteComplexSpectralPowerTrace`: sum of honest finite-dimensional
  traces of the j-th complex-linear blocks;
- `finiteComplexSpectralPowerTrace_tendsto`: finite block trace sums
  approach the real infinite spectral-energy series, embedded into ℂ.

The module is imported into the public `Neoplatonic/LTR/Check.lean`
axiom audit. **Do not treat this v0.47 entry as a passed kernel check
until the current-head action succeeds.**

The mathematical target is:

\[
\lim_{N\to\infty}\sum_{j<N}
\operatorname{Tr}_{\mathbb C^2}
\bigl[(1+4^j+s_j^2)^{-p/2}I_2\bigr]
=\sum_{j=0}^{\infty}2(1+4^j+s_j^2)^{-p/2}.
\]

## Remaining obligations

1. Prove the trace coefficients directly against the full Hilbert
   space's standard orthonormal basis, including summability.
2. Identify the chosen bounded block power with the corresponding
   functional-calculus power of the actual unbounded Dirac operator,
   if a sufficiently expressive spectral calculus is available.
3. Package a rigorous Hilbert-space trace-class certificate (an
   appropriate trace ideal or summable rank-one decomposition).
   Finite-block trace convergence by itself is a partial result.

For this mass growth, convergence for **every** `p > 0` makes the
usual zeta-based spectral-dimension infimum zero, provided the
trace-class identification is completed. The number expresses the
mass-index growth. The earlier Connes-style metric recovery
theorem is an independent statement about the Stone-space metric.
Thus zero spectral dimension should not be read as a proof that
the completed-theory space is discrete or zero-dimensional in every
dimension notion.

The constructive encoding of syntax remains separate from the
classical dense-completion selection used to build the Dirac.
