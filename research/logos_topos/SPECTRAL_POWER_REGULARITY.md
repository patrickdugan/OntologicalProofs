# LTR spectral-power regularity: quantitative analytic targets

**November 4, 2026. Status: written mathematical proofs, with the
full positive-exponent operator-norm continuity theorem already checked
in `ComplexSpectralPowerExponentContinuity.lean`. The quantitative
Lipschitz constants and holomorphic zeta extension below are new
formalization targets and are not Lean-certified.**

## Notation and starting facts

For arbitrary real marked-edge couplings `s_j` set

\[
E_j=1+4^j+s_j^2,\quad h_j=\log E_j\ge0,\quad
w_{p,j}=E_j^{-p/2}=e^{-p h_j/2}.
\]

The actual Hilbert operator is `A_p=⊕_j w_{p,j}I₂`.
The repository verifies the coordinate action, rank-two series,
norm-summable factorization, true `CFC.rpow` equality at all positive
dyadic rational exponents, and local norm continuity of `p↦A_p`
for positive `p`.

## Uniform operator-norm Lipschitz bound

Let `p,q≥δ>0`. By the mean value theorem applied to
`u↦exp(-u h_j/2)`,

\[
|w_{p,j}-w_{q,j}|
\le \frac{|p-q|}{2}h_j e^{-\delta h_j/2}.
\]

The elementary global maximum
`sup_(h≥0) h exp(-δh/2)=2/(eδ)`
therefore gives the *uniform in all edge couplings and all blocks*
bound

\[
\boxed{
\|A_p-A_q\|_{\mathrm{op}}
\le \frac{|p-q|}{e\delta}.
}
\]

The estimate is sharper than a qualitative uniform-series proof;
it uses only the positive diagonal form of the actual Hilbert operator.
The constant is the sharp supremum when the spectral energy variable
is allowed to vary continuously over `[1,∞)`.

## Trace-norm Lipschitz bound

To get a summable derivative majorant, split the exponential:

\[
\frac{h}{2}e^{-\delta h/2}
=e^{-\delta h/4}\,\frac{h}{2}e^{-\delta h/4}
\le \frac{2}{e\delta}e^{-\delta h/4}.
\]

The diagonal scalar trace-norm formula gives

\[
\|A_p-A_q\|_1
=2\sum_{j\ge0}|w_{p,j}-w_{q,j}|.
\]

As `E_j≥4^j`, each `E_j^{-δ/4}≤2^{-jδ/2}`.
Consequently,

\[
\boxed{
\|A_p-A_q\|_1
\le\frac{4|p-q|}
{e\delta\,(1-2^{-\delta/2})}.
}
\]

The mathematical trace norm here uses the trace-class criterion
provided by the summable rank-two series. An abstract trace-ideal
interface and the norm identity are still to be packaged in Lean.

## Spectral zeta function

Define for complex `z` with `Re(z)>0`

\[
\zeta_D(z)=2\sum_{j\ge0}
\exp\bigl(-\tfrac z2\log E_j\bigr).
\]

For any compact set `K⊂\{z:\Re z>0\}`, let
`δ=inf_(z∈K) Re z>0`. Then uniformly for `z∈K`,

\[
|2E_j^{-z/2}|\le 2E_j^{-\delta/2}
\le 2\cdot2^{-j\delta}.
\]

The series converges normally on the right half-plane and hence
is holomorphic there. For every integer `k≥0`,

\[
\boxed{
\zeta_D^{(k)}(z)=
2\left(-\frac12\right)^k
\sum_{j\ge0}(\log E_j)^k E_j^{-z/2}.
}
\]

The convergence of the differentiated series follows from
`h^k e^{-δh/4}≤(4k/(eδ))^k` for `k>0`, together with
the same geometric majorant above. At real `p>0`,
the already verified Hilbert-basis series equals `ζ_D(p)`.

## Implications for the full CFC bridge

Mathlib v4.35.0 supplies `tendsto_cfc_fun` and the isometric
continuous functional calculus. The same scalar Lipschitz estimate
applies uniformly to the spectrum of the positive contraction
`R=(I+D²)⁻¹`. A future Lean theorem should establish

\[
\|\operatorname{CFC.rpow}(R,p/2)
 -\operatorname{CFC.rpow}(R,q/2)\|
\le |p-q|/(e\delta)
\]

for `p,q≥δ>0`. Together with the positive dyadic CFC equality,
density of positive dyadic rationals, and the checked continuity
of `A_p`, this closes

\[
A_p=\operatorname{CFC.rpow}(R,p/2)
\quad\text{for all }p>0.
\]

The `ComplexSpectralDyadicLimits.lean` theorem, once audited,
proves that any sequence of positive dyadic CFC approximants with
exponents tending to `p>0` converges in operator norm to `A_p`.
The direct CFC exponent-continuity theorem and the density witness
remain separate formalization steps.

## Boundary at zero

For the compact infinite-rank resolvent, `0` accumulates in the
spectrum. Positive powers converge **strongly** to the identity as
`p↓0`, while their operator-norm distance from the identity equals
one for every `p>0`. A future audit must state the topology
explicitly. The Lipschitz bounds above depend on `δ>0`; their
constants diverge as `δ↓0`.

## Suggested Lean sequence

1. Prove the scalar inequality using `Real.exp`, `Real.log`,
   and a derivative or mean-value bound.
2. Lift it to `complexBoundedBlockDiagonal` in operator norm.
3. Prove the trace-weight summable difference bound, followed by
   the abstract trace ideal bridge.
4. Transfer the scalar supremum bound through the isometric CFC.
5. Close full positive-real CFC identity by density.
6. Formalize holomorphic normal convergence of `ζ_D` and
   termwise differentiated series.

The constructive syntax encoding and classically chosen dense
complete-type marking remain exactly as in the v0.46 to v0.49
proof ledgers.
