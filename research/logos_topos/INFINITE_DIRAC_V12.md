# LTR v0.12: Compact real spectral metric reconstruction

**Status:** Lean has kernel-verified a self-adjoint complex Dirac operator with compact ordinary resolvent, an exact bounded Hilbert commutator seminorm, and dense-marked Connes-style metric recovery. On compact metric spaces, it has also verified a faithful real continuous-function representation by bounded self-adjoint complex-linear operators.

**Full latest kernel and axiom audit:** https://github.com/patrickdugan/OntologicalProofs/actions/runs/41619858133

## 1. The infinite-dimensional Dirac operator

Let

$$
H=\ell^2(\mathbb N,\mathbb C^2),\qquad
D_j=\begin{pmatrix}2^j&s_j\\s_j&-2^j\end{pmatrix},
\quad s_j\in\mathbb R.
$$

Its maximal domain consists of exactly the Hilbert vectors for which the blockwise image is square-summable. Lean proves density, closedness, and **maximalComplexDiracPMap_isSelfAdjoint**, so $D^*=D$.

The genuine bounded inverse $Q=(D-iI)^{-1}$ is verified through domain-correct two-sided equations. Its finite-rank truncations satisfy

$$
\|Q-Q_N\|\le 2^{1-N}\longrightarrow0.
$$

The theorem **chosenComplexOrdinaryResolvent_isCompact** consequently proves that the ordinary complex resolvent is compact.

[Verified operator theory, LTR v0.10](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41599306612)

## 2. Observable commutators and exact operator norms

A marked real observable $a$ is represented at endpoints $x_j,y_j$ by

$$
\pi_j(a)=\begin{pmatrix}a(x_j)&0\\0&a(y_j)\end{pmatrix}.
$$

The block commutator is

$$
[D_j,\pi_j(a)]=
\begin{pmatrix}
0&s_j(a(y_j)-a(x_j))\\
s_j(a(x_j)-a(y_j))&0
\end{pmatrix}.
$$

Its exact complex Euclidean operator norm is
$|s_j(a(y_j)-a(x_j))|$. The mass parameter disappears.

For uniformly bounded real endpoint values and finite uniform edge-gradient bound $L$, Lean constructs the bounded global operator $C_a$ and proves

$$
\pi(a)\operatorname{Dom}(D)\subseteq\operatorname{Dom}(D),
\qquad D\pi(a)\psi-\pi(a)D\psi=C_a\psi.
$$

The kernel-verified theorem **complexPairCommutator_norm_le_iff** characterizes its optimal norm: for every nonnegative $M$,

$$
\|C_a\|\le M
\quad\Longleftrightarrow\quad
\forall j,\ |s_j(a(y_j)-a(x_j))|\le M.
$$

Because the edge quotients form a nonempty bounded set, the mathematical consequence is

$$
\boxed{\|C_a\|=\sup_j|s_j(a(y_j)-a(x_j))|.}
$$

Lean expresses this through the equivalent least-upper-bound characterization, including **complexHilbertBlock_norm_le_operator**. It does not separately package a supremum equality as a named declaration.

[Verified exact global norm, LTR v0.12](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41616623623)

## 3. Dense-marked Connes-style metric recovery

Assume a metric space $X$ has a countable dense sequence $q:\mathbb N\to X$, with a marked enumeration $(x_j,y_j)$ covering every ordered pair of distinct values of $q$. Set $s_j=1/d(x_j,y_j)$.

The theorem **denseMarkedEdgeUnitBound_iff_lipschitz** extends the unit gradient bound from the marked dense subset to all $X$ by continuity. The theorem **complexDenseMarkedCommutator_norm_le_one_iff_lipschitz** connects it to the norm of the actual bounded complex Hilbert commutator.

The theorem **complexDenseConnesDistance_operator_witness** proves that every admissible continuous real function in the norm-one commutator ball satisfies the metric upper bound, with equality witnessed by $a(z)=d(z,y)$. In its upper-bound-plus-witness formulation, this is

$$
\boxed{d(x,y)=\sup_{\|[D,\pi(a)]\|\le1}|a(x)-a(y)|.}
$$

The operator-norm theorem requires continuous real observables with finite uniform marked gradients. For compact $X$, continuity supplies a bound on the function values as well.

[Verified operator-norm metric recovery](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41617455467)

## 4. Canonical compact real-function representation

For compact $X$, **compactContinuousReal_has_bound** proves any continuous real function has a nonnegative uniform absolute-value bound. **compactContinuousReal_observable_exists** uses the bound to define a bounded complex Hilbert multiplication operator.

**compactRealObservablePi** is a canonical choice of this operator. Lean verifies that it has the desired endpoint action and satisfies:

- **compactRealObservablePi_one**: unit preservation
- **compactRealObservablePi_mul**: multiplication becomes operator composition
- **compactRealObservablePi_add** and **compactRealObservablePi_zero**: additive laws
- **compactRealObservablePi_faithful**: faithfulness when marked endpoints contain a dense sequence
- **compactRealObservablePi_isSelfAdjoint**: real continuous functions are represented by self-adjoint operators

These are properties of operators on the actual infinite-dimensional complex Hilbert space, independent of the auxiliary bound used to construct them.

[Compactness and existence audit](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41618046881), [unital/multiplicative/faithful audit](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41618733759), [additive audit](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41619322035), [self-adjointness audit](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41619858133).

## 5. Exact boundary of the formal theorem

The verified construction provides a complex self-adjoint compact-resolvent Dirac operator, a faithful real-function representation on compact marked spaces, bounded domain-preserving commutators for Lipschitz real observables, and exact metric recovery for dense reciprocal-distance markings.

A standard spectral triple over the full complex commutative C*-algebra still calls for a bundled complex-linear star-algebra homomorphism of complex-valued continuous functions and its domain/commutator laws. The current representation covers the real-valued self-adjoint part.

The intended logical Stone space still needs a constructed compatible dense marking, sentence-labelled clopen reconstruction, and interpretation-map compatibility. Spectral p-summability and effective/functorial claims remain additional formalization work.

The two-point spectral technique has important precedents, including Christensen–Ivan and Pearson–Bellissard. Novelty must concern the proposed effective marked logical reconstruction.

## 6. Verification

The source is committed directly on the default main branch. **Neoplatonic/LTR/Check.lean** audits 340 named declarations. GitHub Actions rejects sorryAx and ofReduceBool and runs the finite reconstruction checks.

[Full passing kernel/axiom/test audit](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41619858133)
