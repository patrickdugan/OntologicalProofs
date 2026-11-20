# Recursive spectral certificates

These Lean modules supply exact statements for repeated linear updates and
spectral analysis of finite observations. Their hypotheses identify the
quantities that an application must justify from a model or an experiment.
The repository pins Lean and Mathlib to v4.35.0.

## General trace–determinant identity

`Neoplatonic.LTR.TraceDeterminant.exp_trace_series_eq_inv_det` proves, for
every finite real square matrix `A` and real `z` satisfying
`‖z • A‖ < 1`, that

\[
\exp\left(\sum_{k=1}^{\infty}
  \frac{z^k\operatorname{tr}(A^k)}{k}\right)
=\det(I-zA)^{-1}.
\]

The norm is the infinity operator norm selected by
`Matrix.Norms.Operator`. The theorem allows arbitrary finite index types,
including the empty type. It imposes no diagonalizability assumption.
`logTrace_hasSum` proves convergence of the displayed logarithm series;
the exponential formula therefore comes with a summability certificate.

The proof first establishes Jacobi's formula at a nonsingular point. A
Neumann series then gives

\[
\sum_{k=0}^{\infty}z^k\operatorname{tr}(A^{k+1})
=\operatorname{tr}((I-zA)^{-1}A).
\]

On a slightly larger interval around zero, a geometric majorant permits
termwise differentiation of the logarithm series. The derivative of its
exponential multiplied by `det(I-zA)` vanishes throughout that interval.
Its value at zero is one, which fixes the integration constant.

For a weighted adjacency matrix, the trace of a power sums the weights of
closed walks of that length. An application to a neural computation needs
an independently justified matrix and a meaning for its entries. The
formal result concerns finite real matrices within the stated norm domain.
Extending the domain to a spectral-radius condition or complex parameters
requires further work.

## Error after repeated approximate transport

Let `E = B*L - L*A`. The theorem `power_defect_sum` gives the identity

\[
B^nL-LA^n=\sum_{j=0}^{n-1}B^jEA^{n-1-j}
\]

in every ring, with the multiplication order preserved.
The estimates in `Neoplatonic.LTR.ApproximateIntertwining` assume a
submultiplicative norm with `‖1‖ = 1`. Continuous endomorphisms of a
nontrivial normed space provide a suitable setting.

If `‖A‖ ≤ α`, `‖B‖ ≤ β`, and `‖E‖ ≤ ε`, then

\[
\|B^nL-LA^n\|
\le\varepsilon\sum_{j=0}^{n-1}\beta^j\alpha^{n-1-j}.
\]

The common-radius corollary gives
`‖B^n*L - L*A^n‖ ≤ n*ρ^(n-1)*ε` when both operator norms are at most
`ρ`. At depth zero, the result states that both sides vanish.
Nonexpansive operators yield a bound of `n*ε`. When `‖A‖ ≤ 1` and
`‖B‖ ≤ ρ < 1`, `norm_power_defect_le_geometric` gives the uniform bound
`ε/(1-ρ)` at every depth. If both operators satisfy the same strict
contraction bound, `power_defect_tendsto_zero` proves that the defect tends
to zero.

These bounds help choose a depth at which a measured transport error stays
within tolerance. The application must supply the operator norm bounds and
an error certificate. The current formulation uses one operator algebra;
transport between spaces of different dimensions needs a composition-based
extension.

## Walsh coefficients and exact residual energy

`Neoplatonic.LTR.WalshFourier` represents the cube recursively:
`Cube 0 = Unit` and `Cube (n+1) = Bool × Cube n`. It proves that the cube
has `2^n` elements. A recursive Walsh–Hadamard transform is connected to
the explicit parity-character formula

\[
\widehat f(s)=2^{-n}\sum_{x\in\{0,1\}^n}
  f(x)(-1)^{\langle s,x\rangle}.
\]

The theorem `parseval` proves

\[
\sum_s\widehat f(s)^2
=2^{-n}\sum_x f(x)^2.
\]

For any real functions `f` and `g` on that cube, `residual_energy` yields

\[
2^{-n}\sum_x(f(x)-g(x))^2
=\sum_s(\widehat f(s)-\widehat g(s))^2.
\]

`coefficient_error_le` bounds each squared coefficient discrepancy by that
total error. This supports exact accounting of an approximation's error
after its values on a Boolean intervention space have been specified.
The measure is uniform over the entire cube. Sampling from another
distribution needs a separate statistical or weighted-Fourier argument.

## Earlier certificates and kernel checks

`RecursiveSpectral.lean` contains the Hankel factorization and rank bound,
exact intertwining of matrix powers, characteristic-polynomial preservation
under invertible transport, and the two-state geometric zeta series.

The workflow `.github/workflows/recursive-spectral-lean.yml` builds all four
modules. It also runs `scripts/check_recursive_spectral.py`, which reads
their named declarations and generates a complete `#print axioms` manifest.
Every declaration must produce one report. Each dependency must belong to
the set `propext`, `Classical.choice`, `Quot.sound`. The check rejects
missing reports, duplicate reports, added dependencies, and Lean errors.
The manifest and Lean output are uploaded as artifacts.

The source check rejects proof placeholders and unsafe constructs. Its
supported declaration forms are explicit; unsupported forms require an
audit update. Regression tests cover the failure cases, including the
source-check bug from the earlier workflow.

To run the same checks from the repository root:

```bash
lake build Neoplatonic.LTR.RecursiveSpectral Neoplatonic.LTR.ApproximateIntertwining Neoplatonic.LTR.WalshFourier Neoplatonic.LTR.TraceDeterminant
python3 -m unittest discover -s scripts -p 'test_recursive_spectral_audit.py' -v
python3 scripts/check_recursive_spectral.py
```

## Primary implementation sources

The proofs use the pinned Mathlib sources for
[matrix norms](https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/Analysis/Matrix/Normed.lean),
[geometric series](https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/Analysis/SpecificLimits/Normed.lean),
and [finite sums](https://github.com/leanprover-community/mathlib4/blob/v4.35.0/Mathlib/Data/Fintype/BigOperators.lean).
The Lean files give the exact hypotheses and declarations used in each proof.
