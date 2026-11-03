# LTR v0.17: A dense complex spectral triple with exact marked metric recovery

Date: November 3, 2026

## Status

**Kernel-verified.** The construction in
[`Neoplatonic/LTR/ComplexMetricSpectralTriple.lean`](../../Neoplatonic/LTR/ComplexMetricSpectralTriple.lean)
passed the dedicated Lean build, axiom audit, and finite regression tests in
[GitHub Actions run 41644762120](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41644762120).

The dense complex Lipschitz star subalgebra in
[`ComplexLipschitzAlgebra.lean`](../../Neoplatonic/LTR/ComplexLipschitzAlgebra.lean)
passed in [run 41644193781](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41644193781).

## Operator construction

Let (X) be a compact metric space, (q:\mathbb N\to X) have dense range,
and (x_j,y_j\in X) be marked endpoints with (x_j\neq y_j).
Assume every value of (q) occurs among the marked endpoints, so that
the representation is faithful.

Define:

- (A=C(X,\mathbb C)).
- (A_0=\operatorname{Lip}(X,\mathbb C)), the complex functions admitting some finite global Lipschitz bound.
- (H=\ell^2(\mathbb N,\mathbb C^2)).
- (\pi(f)_j=\mathrm{diag}(f(x_j),f(y_j))).
- (s_j=d(x_j,y_j)^{-1}) and (D_j=\bigl(\begin{smallmatrix}2^j&s_j\\s_j&-2^j\end{smallmatrix}\bigr)).
- (D) is the maximal-domain blockwise unbounded operator.
- (Q=(D-iI)^{-1}), the actual ordinary resolvent with verified two-sided equations.

The `CompactComplexSpectralTriple` Lean record contains the algebra, representation,
Dirac and ordinary resolvent, with proofs of:

1. Uniform density of (A_0\subset C(X,\mathbb C)) by complex Stone–Weierstrass.
2. Injectivity of the bundled complex star-algebra homomorphism (\pi).
3. Density of the maximal Dirac domain, closedness and self-adjointness of (D).
4. Compactness of (Q), including the two inverse identities for (D-iI).
5. For every (f\in A_0), invariance of the maximal domain under (\pi(f)),
   and a bounded complex Hilbert operator (C_f) extending ([D,\pi(f)]).

The mass sequence (2^j) enforces compact resolvent for arbitrary real
edge-coupling sequences. The exact commutator norms are independent of
the diagonal masses.

## Metric reconstruction

Additionally assume the edge list covers every ordered pair of *distinct*
values of the dense sequence (q).

Then the verified metric-recovery theorem states that for every (x,y\in X),

[
d(x,y)=\sup\{\lvert f(x)-f(y)\rvert:
 f\in A_0,\ \|[D,\pi(f)]\|\le 1\}.
]

The supremum is attained by (f_y(z)=d(z,y)), viewed as a complex-valued
Lipschitz function. Lean proves the upper bound and the attaining witness.
The actual operator commutator equals the bounded extension on the
maximal Dirac domain.

## Formal declarations

- `compactComplexLipschitzStarSubalgebra`
- `complexDistanceToPoint_mem_lipschitz`
- `compactComplexLipschitz_separatesPoints`
- `compactComplexLipschitz_dense`
- `compactComplexLipschitz_has_commutator_bound`
- `CompactComplexSpectralTriple`
- `compactComplexMarkedSpectralTriple`
- `compactComplexMarkedSpectralTriple_metric_recovery`

## Limits and next obligations

The theorem is conditional on a compact metric space, a countable dense
marking and its coverage properties. The repository still needs an
explicit, effective marked enumeration for the intended logical Stone
completion spaces, with compatibility under translations of theories.

The construction uses exponential diagonal masses and therefore
suggests a very small spectral dimension. No p-summability or
dimension-spectrum theorem is claimed here, nor any functorial
invariance of the metric under arbitrary logical interpretations.

The result is a spectral-triple foundation for the mathematical
Logos–Topos program. Logical label reconstruction, effective
complexity, and theological consequences require separate theorems.
