# LTR v0.49: Real CFC powers and quantitative exponent stability

**Date:** November 4, 2026

## Verified kernel results

The current operator is the explicit maximal-domain complex Dirac
on `H = ℓ²(ℕ, ℂ²)`, with `D_j² = (4^j+s_j²)I₂`.
Its bounded squared resolvent is `R=(I+D²)⁻¹` and
`R_j = (1+4^j+s_j²)⁻¹I₂`.

V0.49 extends the checked v0.48 positive-exponent semigroup
`A_p A_q=A_(p+q)` by identifying positive operators and the
genuine continuous functional calculus of the actual Hilbert map.

- [Run 41784940701](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41784940701):
  `ComplexSpectralPowerPositive.lean` kernel proves that every `A_p` for
  `p>0` is self-adjoint and positive in the actual Hilbert-operator sense.
  The same is checked for `R`.
- [Run 41792546725](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41792546725):
  `ComplexSpectralCFCSqrt.lean` kernel proves the CFC square-root theorem,
  the real CFC half-exponent theorem, and repeated square roots.
  In particular, `A_(2/2^n)=CFC.rpow R ((1/2)^n)`.
- [Run 41793916592](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41793916592):
  `ComplexSpectralCFCDyadicRational.lean` proves the integer-power
  semigroup rule and extends the CFC identity to every positive
  dyadic rational exponent.
- [Run 41831403870](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41831403870),
  at source commit `4de8d6115ddc21922b1cfc9f843673159f31f7a6`:
  `ComplexSpectralCFCReal.lean` proves the identity for every
  positive real exponent. `RealPowerExponentStability.lean` and
  `ComplexSpectralPowerLipschitz.lean` prove the quantitative
  scalar, diagonal-operator, and CFC bounds below. All ten new
  public declarations passed the axiom audit using only
  `propext`, `Classical.choice`, and `Quot.sound`.

All cited runs passed the LTR Lean build, dependency/axiom audit,
and finite reconstruction tests. Their statements appear in
`Neoplatonic/LTR/Check.lean`.

## Verified operator identities

For each `p>0`, Lean verifies

\[
A_p=A_p^*,\quad A_p\ge0,\quad
A_{p/2}=\operatorname{sqrt}_{\mathrm{CFC}}(A_p).
\]

At `p=2` this specializes to the actual Dirac squared resolvent:

\[
A_1=\operatorname{sqrt}_{\mathrm{CFC}} R
=R^{1/2}_{\mathrm{CFC}}.
\]

For every `n\in\mathbb N` and positive natural `k`:

\[
\boxed{
 A_{2k/2^n}=R^{k/2^n}_{\mathrm{CFC}}.
}
\]

The theorem quantifies over arbitrary real edge couplings.
The CFC on the right is Mathlib's operator-algebra construction,
with its pinned instances explicitly registered. The identity
holds in the entire infinite-dimensional operator algebra.

## Verified extension to every positive real exponent

`ComplexSpectralCFCReal.lean` closes the real-exponent bridge.
The proof uses the established continuity of the concrete family,
then proves CFC continuity and supplies an explicit dyadic sequence.

Fix `p₀>0`. For all nearby `p\ge p₀/2`,
let `B_{p,j}` be the verified rank-two coordinate blocks.
They satisfy the uniform summable majorant

\[
\|B_{p,j}\|
\le (1+4^j+s_j^2)^{-p/2}
\le 2^{-j p_0/2}.
\]

Each `p\mapsto B_{p,j}` is operator-norm continuous, since its
coefficient is the positive real base
`(1+4^j+s_j²)⁻¹` raised to `p/2`.
The Weierstrass M-test gives locally uniform operator-norm
convergence of `\sum_j B_{p,j}` in `p`, so `p\mapsto A_p`
is continuous on `(0,\infty)`.

On the CFC side, the positive contraction `R` has compact spectrum
contained in `[0,1]`. The function
`(t,p)\mapsto t^{p/2}` is continuous on the product of
`[0,1]` with each compact positive-exponent interval,
including `t=0`. Compactness supplies uniform continuity
in the spectrum variable. The continuous CFC homomorphism
therefore makes `p\mapsto R^{p/2}_{\mathrm{CFC}}`
operator-norm continuous on `(0,\infty)`.

For the mesh `d_n=2/2^n`, Lean constructs the upper approximants

\[
p_n=d_n\left(\left\lfloor p/d_n\right\rfloor+1\right),
\qquad 0\le p_n-p\le d_n\longrightarrow0.
\]

The positive dyadic CFC operators converge to `A_p` by the earlier
dyadic-limit theorem and to `CFC.rpow R (p/2)` by CFC continuity.
Uniqueness of the operator-norm limit gives

\[
\boxed{A_p=R^{p/2}_{\mathrm{CFC}},\qquad p>0.}
\]

The kernel theorem is `chosenComplexSpectralPower_eq_CFC_rpow`.
Its premises are an arbitrary real coupling sequence and `p>0`.
The proof includes spectral value zero in the joint scalar continuity
argument and works in the full infinite-dimensional operator algebra.

## Endpoint warning: exponent zero

Although `R_j>0` for each individual block, the weights
tend to zero as `j\to\infty`. Hence `0` is an accumulation
point of the spectrum of the compact operator `R`.

At `p=0`, the CFC convention gives `R^0=I`.
For every `p>0`, the concrete positive contraction satisfies

\[
\|A_p-I\|=\sup_{j\ge0}
  \bigl(1-(1+4^j+s_j^2)^{-p/2}\bigr)=1.
\]

For each fixed Hilbert coordinate the weights converge to one
as `p\downarrow0`, and dominated convergence in `ℓ²`
gives strong convergence `A_p\psi\to\psi`.
Thus the real-power family is strongly continuous at zero
but discontinuous there in operator norm. This endpoint
observation is a written argument requiring its own Lean
formalization.

## Further verified operator-norm continuity and CFC-limit results

The initial v0.49 ledger identified locally uniform convergence as
the next analytic obligation. Both the summability hypotheses and
the actual global operator continuity are now kernel checked.

- [Run 41825084247](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41825084247):
  `ComplexSpectralPowerExponentContinuity.lean` verifies
  `chosenComplexSpectralPowerTotal_continuousOn_positive`.
  The extension agrees with the true `A_p` at every `p>0`,
  and is operator-norm continuous on every half-line
  `[p₀/2,∞)` for `p₀>0`.
- [Run 41826219905](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41826219905):
  `ComplexSpectralDyadicLimits.lean` verifies
  `chosenComplexSpectralDyadicRational_CFC_tendsto`.
  Given *any* sequence of positive dyadic exponents whose
  corresponding spectral-power exponents converge to `p>0`,
  the actual CFC dyadic operator approximants converge
  in operator norm to `A_p`.

The second result supplies one limit in the full real-exponent
proof. `chosenComplexSquaredResolvent_CFC_rpow_continuousOn` and
`exists_complexSpectralDyadicRational_tendsto` now supply the
CFC continuity and dyadic approximation obligations.

## Verified scalar-to-operator stability transfer

[Run 41827146368](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41827146368)
checks the new `ComplexSpectralPowerStability.lean` module.
For positive `p,q` and an arbitrary nonnegative real `K`,
the kernel now verifies

\[
\Bigl(\forall j, |w_{p,j}-w_{q,j}|\le K\Bigr)
\implies \|A_p-A_q\|_{\mathrm{op}}\le K.
\]

It also verifies that the full operator difference is exactly
the bounded Hilbert diagonal whose coefficients are
`w_{p,j}-w_{q,j}`. This makes a scalar sharp Lipschitz
estimate sufficient to obtain the global operator estimate.

## Verified quantitative bound

`RealPowerExponentStability.lean` proves, for `0≤x≤1` and
`p,q≥δ>0`,

\[
|x^{p/2}-x^{q/2}|\le\frac{|p-q|}{e\delta}.
\]

The proof uses the exponential tangent inequality and Mathlib's
`Real.mul_exp_neg_le_exp_neg_one`, with a separate scalar-zero case.
`ComplexSpectralPowerLipschitz.lean` lifts the estimate through the
verified diagonal norm bound. The full CFC identity yields

\[
\boxed{\|A_p-A_q\|
=\|R^{p/2}_{\mathrm{CFC}}-R^{q/2}_{\mathrm{CFC}}\|
\le\frac{|p-q|}{e\delta}.}
\]

The constant is uniform over all blocks and all real coupling
sequences. The final theorem is
`chosenComplexSquaredResolvent_CFC_rpow_sub_norm_le`.
`Check.lean` audits the scalar helpers, continuity and approximation
theorems, universal CFC equality, and both operator bounds.

The local trace-norm estimate and holomorphic spectral-zeta
construction in the [regularity note](SPECTRAL_POWER_REGULARITY.md)
remain written proofs awaiting Lean formalization.

## Next formal milestones

1. Distinguish the operator-norm discontinuity and strong continuity
   at exponent zero.
2. Build a generic trace-ideal interface, plus the
   holomorphic spectral-zeta and differentiated-series statements.

The constructive logical syntax map and the classically chosen
dense complete-type marking remain as described in v0.48.

## Reproduce

```sh
lake build Neoplatonic.LTR.Check
lake env lean Neoplatonic/LTR/Check.lean
python3 -m unittest discover -s research/logos_topos -p 'test_*.py' -v
```
