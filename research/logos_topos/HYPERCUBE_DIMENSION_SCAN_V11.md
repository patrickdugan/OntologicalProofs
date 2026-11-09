# LTR-MAN-11: Six- and seven-dimensional Dirac metric search

**Experiment date:** 2026-11-09. **Status:** reproducible CPU numerical experiment, with independently checked frozen candidate matrices. The four- and five-dimensional obstruction remains a written mathematical argument awaiting a Lean matrix certificate.

## Mathematical target

For a faithful representation of \(A=\mathbb C^4\) on \(\mathbb C^N\), let
\[
\pi(f)=\operatorname{diag}(f_{\ell_1},\ldots,f_{\ell_N}),
\qquad\ell_i\in\{00,01,10,11\},
\]
with every truth profile represented at least once. The Dirac matrix \(D=D^*\in M_N(\mathbb C)\) may have arbitrary couplings between different truth sectors. Its Connes distance is computed by minimizing \(\|[D,\pi(f)]\|\) subject to \(f(a)=0,f(b)=1\) and then taking the reciprocal.

The inner minimization may be restricted to **real** \(f\): phase-rotate the relevant endpoint difference to a positive real number and take the real part. The Hermitian operator-norm commutator cannot increase under this map.

The target ordered distances are
\[
(d_{01},d_{02},d_{13},d_{23},d_{03},d_{12})
=(1,1,1,1,2,2).
\]

Because multiplying \(D\) by a positive scalar divides all distances by that scalar, remove the global scale by minimizing centered log errors:
\[
\epsilon(D)=\sqrt{\frac16\sum_{a<b}
\left[\log\frac{d_D(a,b)}{d_H(a,b)}-\overline{\log(d_D/d_H)}\right]^2}.
\]
The objective is zero exactly when the six approximate distances match Hamming up to global scale. A numerical optimizer reaching zero would require an independent high-precision and analytic certificate.

## Implemented search

- **Outer:** L-BFGS-B over independent inter-sector Dirac coefficients. For real-symmetric \(D\), each unordered pair of different sectors contributes one real variable. For complex Hermitian \(D\), it contributes one real and one imaginary variable.
- **Inner:** two-start Nelder–Mead minimization of the largest absolute eigenvalue of the Hermitian commutator \(i[D,\pi(f)]\), with the selected endpoint difference fixed to one.
- **Gradient:** the envelope-theorem derivative of a simple extremal eigenvalue, using one subgradient at eigenvalue ties. The global objective is nonconvex and the chosen subgradient can be unstable at ties.
- **Initialization:** merge selected equal-truth coordinates of the verified eight-dimensional independent-edge model, or use an arbitrary faithful multiplicity pattern with graph-edge initialization. A small random perturbation is driven by an explicit seed.
- **Validation:** reconstruct the frozen Dirac matrices separately and minimize all six dual distance problems again with additional inner starts and tighter stopping tolerances.

The full independent-edge control returns exactly the Hamming distance vector within numerical tolerance.

## Results

All distances below are globally scale-adjusted.

| Hilbert dimension | Search family | Seed | Log-distance RMSE | Scaled distance vector |
|---:|---|---:|---:|---|
| 6 | Real Hermitian, merged \((0,1)\) | 1 | 0.135451 | (1.22309, 1.08133, 1.07032, 0.99511, 1.69540, 1.67488) |
| 7 | Real Hermitian, merged \((0)\) | 3 | 0.122079 | (1.14616, 1.13243, 1.01772, 1.02850, 1.82264, 1.61536) |
| 6 | Complex Hermitian, merged \((0,1)\) | 2 | 0.142251 | (1.19201, 1.08078, 1.07447, 1.06505, 1.65614, 1.63826) |
| 7 | Complex Hermitian, merged \((0)\) | 2 | 0.119290 | (1.13448, 1.14054, 1.02383, 1.02000, 1.81667, 1.62948) |
| 8 | Independent edge-block control | n/a | 0 | (1, 1, 1, 1, 2, 2) |

The six-dimensional complex run is a separate local optimum. A complex Hermitian search includes real-symmetric matrices as a special case, so its global optimum can only improve on the best real-symmetric optimum.

Independent re-evaluation of the frozen 6D real and 7D complex matrices reproduced the archived distance vectors with maximum absolute discrepancies of approximately \(1.8\times10^{-7}\) and \(4.5\times10^{-8}\), respectively. These are small numerical consistency residuals, **not** proofs of global optimality.

## Additional multiplicity structures

Positive integer sector multiplicities summing to six or seven fall into the following types, modulo square symmetries:

| N | Pattern | Best observed real log-RMSE in short two-seed scan |
|---:|---|---:|
| 6 | (3,1,1,1) | 0.2830 |
| 6 | (2,2,1,1), doubled adjacent | 0.1501 |
| 6 | (2,1,1,2), doubled opposite | 0.1501 |
| 7 | (4,1,1,1) | 0.1624 |
| 7 | (3,2,1,1), larger sectors adjacent | 0.1502 |
| 7 | (3,1,1,2), larger sectors opposite | 0.1503 |
| 7 | (2,2,2,1) | 0.1221, in a richer merged-edge initialization |

These are small, non-exhaustive local searches and depend on initialization. Their positive errors cannot exclude an exact lower-dimensional construction.

## Frozen candidate matrices and independent check

Files:
- `hypercube_6d_7d_candidates.json` contains labels, a Hermitian upper triangle, globally fitted couplings, distances, and solver provenance for the two independently validated candidates.
- `verify_hypercube_candidates.py` reconstructs their full matrices, checks Hermiticity, re-evaluates every distance, and checks against the archived values.
- `hypercube_metric_capacity_search.py` now supports seeded multistart real couplings.
- `hypercube_complex_metric_search.py` searches complex Hermitian couplings and multiple multiplicity patterns.

Run from the repository root:

```bash
python research/logos_topos/verify_hypercube_candidates.py
python research/logos_topos/hypercube_metric_capacity_search.py --dims 6 7 --seeds 0 1 3 --maxiter 40
python research/logos_topos/hypercube_complex_metric_search.py --dims 6 7 --seeds 0 1 2 --maxiter 60
python research/logos_topos/hypercube_complex_metric_search.py --dims 6 7 --partitions --all-merges --seeds 0 1 --maxiter 60
```

Requires NumPy and SciPy. It is intentionally a manual research gym; the full stochastic nested optimizer is not placed in lightweight repository CI.

## Spectral constraints for an analytic 6D/7D decision

The **written no-go argument for dimensions at most five** is recorded in `HYPERCUBE_FOUR_DIMENSION_NO_GO_V10.md`. It uses the two coordinate commutators
\[
A=i[D,\pi(p)],\qquad B=i[D,\pi(q)].
\]

Exact Hamming geometry forces
\[
\|A+B\|\le1,\quad\|A-B\|\le1,
\quad\|A\|=\|B\|=1.
\]
Because \(A\pm B\) are Hermitian contractions,
\[
(A+B)^2\preceq I,\qquad(A-B)^2\preceq I.
\]
Adding them yields
\[
\boxed{A^2+B^2\preceq I.}
\]
This operator inequality is a useful necessary condition for the remaining dimensions. It forces the two commutators to annihilate each other's unit-eigenvalue eigenspaces. In dimension at most five, the small residual spectral subspace then leads to the zero-product obstruction detailed in the written proof.

For six and seven dimensions, the residual subspace can support further nontrivial couplings. The next rigorous task is to characterize those couplings together with the requirement that every Hamming-one dual evaluation have norm one.

A sensible next formal target in Lean is the **parallelogram contraction lemma** for bounded self-adjoint operators, followed by explicit 6D/7D finite block-multiplicity case splits. The numerical candidate files can serve as counterexample tests for overly strong proposed lower bounds.

**Current mathematical status:** \(6\le r_{\mathrm{geom}}(2)\le8\) under the written no-go proof; the Hamming-edge 8D realization is already Lean verified in MAN-09. The 6D/7D numerical experiments have not established feasibility or ruled it out.
