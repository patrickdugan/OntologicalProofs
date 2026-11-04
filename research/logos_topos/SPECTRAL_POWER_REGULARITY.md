# LTR spectral-power regularity: quantitative analytic targets

**November 4, 2026. Status: the full positive-real CFC identity and
the operator-norm Lipschitz bound are formalized in
`ComplexSpectralCFCReal.lean` and `ComplexSpectralPowerLipschitz.lean`.
The trace-norm estimate and holomorphic zeta extension below remain
written mathematical proofs awaiting Lean formalization.**

The operator results passed the Lean build, axiom audit, and finite
reconstruction suite in
[run 41831403870](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41831403870),
at source commit `4de8d6115ddc21922b1cfc9f843673159f31f7a6`.

## Notation and starting facts

For arbitrary real marked-edge couplings `s_j` set

\[
E_j=1+4^j+s_j^2,\quad h_j=\log E_j\ge0,\quad
w_{p,j}=E_j^{-p/2}=e^{-p h_j/2}.
\]

The actual Hilbert operator is `A_p=⊕_j w_{p,j}I₂`.
The repository verifies the coordinate action, rank-two series,
norm-summable factorization, true `CFC.rpow` equality at all positive
real exponents, and the quantitative norm continuity of `p↦A_p`
for positive `p` described below.

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

`real_rpow_half_exponent_sub_le` proves the scalar estimate, including
base zero, using exponential inequalities. The theorem
`chosenComplexSpectralPower_sub_norm_le_lipschitz` lifts it to the
actual Hilbert operator. The earlier uniform-series proof also remains
available as an independent route to qualitative continuity.
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

## Completed CFC bridge

`ComplexSpectralCFCReal.lean` proves joint scalar continuity on
the compact spectrum for positive exponents, then applies the
continuous CFC homomorphism. Explicit upper dyadic approximants
and uniqueness of the norm limit give

\[
A_p=\operatorname{CFC.rpow}(R,p/2),\qquad p>0.
\]

Rewriting the established diagonal estimate through this equality
gives the checked theorem
`chosenComplexSquaredResolvent_CFC_rpow_sub_norm_le`:

\[
\|\operatorname{CFC.rpow}(R,p/2)
 -\operatorname{CFC.rpow}(R,q/2)\|
\le |p-q|/(e\delta)
\]

for `p,q≥δ>0`. The continuity proof includes spectral value zero.
`ComplexSpectralDyadicLimits.lean` supplies the earlier theorem
that every convergent positive dyadic CFC sequence has limit `A_p`.

## Boundary at zero

For the compact infinite-rank resolvent, `0` accumulates in the
spectrum. Positive powers converge **strongly** to the identity as
`p↓0`, while their operator-norm distance from the identity equals
one for every `p>0`. A future audit must state the topology
explicitly. The Lipschitz bounds above depend on `δ>0`; their
constants diverge as `δ↓0`.

## Remaining Lean targets

1. Prove the trace-weight summable difference bound, followed by
   the abstract trace ideal bridge.
2. Formalize holomorphic normal convergence of `ζ_D` and
   termwise differentiated series.
3. Formalize strong continuity and the operator-norm gap at zero.

The constructive syntax encoding and classically chosen dense
complete-type marking remain exactly as in the v0.46 to v0.49
proof ledgers.
