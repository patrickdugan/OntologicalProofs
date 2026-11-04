# LTR v0.47: Hilbert-basis spectral trace and nonnegative threshold

**Date:** November 4, 2026.

## Kernel verification

The finite-rank spectral-power construction and its trace limit
passed [LTR CI 41776336079](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41776336079)
on commit `a653362`.

The actual infinite-Hilbert-space basis-diagonal identity,
basis-block summability and agreement with the scalar global trace
passed [LTR CI 41777045850](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41777045850)
on commit `cffda9c`.

The separate p=0 divergence and threshold additions are staged in
`ComplexSpectralBasisTrace.lean`. Their kernel verification is
pending the next complete CI run.

All named theorem audits reside in `Neoplatonic/LTR/Check.lean`.

## Concrete operator and finite-rank trace

On `H = ℓ²(ℕ,ℂ²)`, the verified bounded map `A_p`
has the j-th block

\[
A_{p,j}=w_p(j)I_2,\qquad
w_p(j)=(1+4^j+s_j^2)^{-p/2}.
\]

The code constructs literal finite-rank Hilbert operators
`finiteComplexSpectralPower scale p N` and verifies their
coordinate action. Their finite-block traces converge:

\[
\lim_{N\to\infty}\sum_{j<N}\operatorname{Tr}_{\mathbb C^2} A_{p,j}
=\sum_{j=0}^\infty 2w_p(j).
\]

[Source](../../Neoplatonic/LTR/ComplexSpectralGlobalTrace.lean).

## Actual Hilbert-space diagonal coefficients

For `e_{j,k}` the concrete standard unit vectors in the
j-th ℂ² summand, Lean verifies directly from the *global operator*

\[
\langle e_{j,k}, A_p e_{j,k}\rangle=w_p(j).
\]

The function `complexSpectralBasisBlockTrace` groups these two
Hilbert-space coefficients. The kernel proves that its values
equal the existing scalar trace terms, that the complex series
is summable for p > 0, and that

\[
\sum_{j=0}^\infty\sum_{k=0}^1
\langle e_{j,k}, A_p e_{j,k}\rangle
=\sum_{j=0}^\infty 2(1+4^j+s_j^2)^{-p/2}.
\]

[Source](../../Neoplatonic/LTR/ComplexSpectralBasisTrace.lean).

## Analytic trace-class conclusion and quantitative bound

For p > 0 the verified weight comparison gives

\[
0\le w_p(j)\le 2^{-jp},\qquad
2\sum_jw_p(j)\le\frac{2}{1-2^{-p}}.
\]

Each block is positive scalar with two repeated singular values
w_p(j). Because the canonical ℓ² direct sum is spanned by its
coordinate unit vectors, the Hilbert-space operator has a
summable rank-one expansion

\[
A_p=\sum_{j\ge0}\sum_{k=0}^1
w_p(j)\,|e_{j,k}\rangle\langle e_{j,k}|,
\]

convergent in trace norm. Thus the actual block-diagonal operator
is trace class by the standard Hilbert-space characterization.

**Proof-fidelity boundary:** the rank-one decomposition,
trace-norm statement and generic trace-ideal packaging above are
currently a *written analytic argument*, not an abstract Lean
`TraceClass` instance. Mathlib v4.35.0 supplies the
finite-dimensional `LinearMap.trace` used in the checked block
identities; the project also proves the full basis-diagonal sum.
The exact identification with the functional-calculus power
`(1+D²)^(-p/2)` has likewise not been formalized as a
general unbounded operator functional-calculus theorem.

At p=0 the two unit values per block cause divergence. A Lean
lemma for this boundary is included in the staged source and
requires the pending audit.

## Geometric consequence

The existing
`complexDirac_complexObservableBlock_commutator_norm`
establishes for any diagonal mass m and marked edge coupling s:

\[
\|[D_{m,s},\operatorname{diag}(a,b)]\|
=|s|\,\|b-a\|.
\]

The diagonal mass cancels from the Lipschitz seminorm. The
eigenenergy satisfies `D_{m,s}²=(m²+s²)I₂`.
Fast-growing masses therefore reduce spectral trace tails
without changing the Connes-style distance recovered by the
marked commutators.

The p > 0 convergence and the p=0 divergence give zero
nonnegative zeta-summability threshold. This is a property
of the mass spectrum. It leaves open the exact comparison with
Hausdorff or other metric dimensions of the completed-theory
Stone space.

The syntax-numbered sentence encoding is constructive;
the selected sequence of complete theories marking the
Dirac blocks remains classical.

## Reproduce

```sh
lake build Neoplatonic.LTR.Check
lake env lean Neoplatonic/LTR/Check.lean
python3 -m unittest discover -s research/logos_topos -p 'test_*.py' -v
```
