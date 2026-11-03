# LTR-07: Infinite Dirac reconstruction, analytic and Lean proof ledger

## 1. Operator and domain

Let X be a compact metrizable Stone completion space whose distinct points
are separated by the marked logical observations. Let Q⊂X be a countable
dense set and enumerate all unordered pairs of distinct points
(x_j,y_j) from Q. Set d_j=d(x_j,y_j)>0.

Work on the complex Hilbert direct sum H=⊕_(j≥0) C². For each j define

    s_j = 1/d_j,
    m_j = 2^j,
    D_j = [[m_j,s_j],[s_j,-m_j]].

Every D_j is self-adjoint, with

    D_j² = μ_j² I,  μ_j² = m_j²+s_j² ≥4^j.

Define the maximal direct-sum domain

    Dom(D)={ψ∈H : Σ_j μ_j² ||ψ_j||² <∞}
    (Dψ)_j=D_j ψ_j.

Finite-support vectors lie in Dom(D), making D densely defined. The
maximal-domain graph norm is equivalent to
Σ_j(1+μ_j²)||ψ_j||². Completeness of this weighted ℓ² space makes
the direct-sum operator closed.

For each j the matrices D_j±iI are invertible and their inverses have
norm 1/sqrt(1+μ_j²)≤1. The blockwise inverse extends to bounded maps on
H. Their ranges lie in Dom(D), since
μ_j²/(1+μ_j²)≤1. Thus D±iI are surjective from Dom(D) to H.
A densely defined symmetric operator with both of these resolvent
surjectivity properties is self-adjoint.

This is a complete classical analytic argument. Its finite-support
matrix lemmas, bounded Hilbert diagonal map, and compactness estimates
are being formalized in Lean. The domain, closedness, and adjoint
criterion have not yet been kernel formalized.

## 2. Compact squared resolvent: the verified construction

The squared resolvent R=(I+D²)^(-1) acts as the bounded scalar block map

    Rψ_j = w_j ψ_j,  w_j=(1+4^j+s_j²)^(-1).

The bounded operator is implemented on an actual real Hilbert space

    H_R = lp (fun _ : Nat => EuclideanSpace Real (Fin 2)) 2,

through mathlib's lp.mapCLM, in
Neoplatonic/LTR/BoundedHilbertDiagonal.lean and
Neoplatonic/LTR/HilbertResolventWeights.lean.

Let P_N retain the first N blocks. Its complement gives the exact tail

    R_>=N ψ_j = w_j ψ_j for j≥N, 0 otherwise.

Lean proves the numerical and operator estimates

    0 ≤ w_j ≤ (1+4^j)^(-1),
    ||R_>=N|| ≤ (1+4^N)^(-1) → 0.

The finite-rank approximation R_N consists of a finite sum of operators

    single_j ∘ (w_j id) ∘ eval_j,  j<N.

Each eval_j has finite-dimensional range and is compact, hence every
finite block operator is compact. So R_N is compact.

The final identification is

    R_N = R - R_>=N,

whence

    ||R-R_N|| ≤ (1+4^N)^(-1).

By mathlib's norm-closed compact-operator theorem,
R is compact. The module InfiniteSquaredResolventCompact.lean is
the single authoritative kernel-checked proof of this theorem.
The full audit passed in GitHub Actions run 41580149320, and a
later combined audit with the finite-block Hilbert density theorem
passed in run 41580342867.

The statement proved concerns an *actual bounded compact candidate* for
(I+D²)^(-1) on the real Hilbert sum. Identifying it as the inverse of an
unbounded maximal-domain D needs the domain theorem from section 1.

## 3. Compact resolvent and spectral summability

Once D is self-adjoint, (D-iI)^(-1) is block-diagonal and has block norms

    ||(D_j-iI)^(-1)||=(1+μ_j²)^(-1/2)≤(1+4^j)^(-1/2).

Therefore its finite-rank truncations converge in operator norm and
its resolvent is compact.

For every real p>0,

    Tr((I+D²)^(-p/2))
      =2Σ_j(1+μ_j²)^(-p/2)
      ≤2Σ_j 2^(-jp)<∞.

The spectral triple is thus p-summable for every p>0 for the chosen
exponentially growing diagonal mass. This is an intentional property
of the chosen spectral implementation, not an intrinsic invariant of
a logical theory; changing mass terms leaves the commutator seminorm
unchanged while changing eigenvalue growth.

## 4. Commutator seminorm and metric

Represent any continuous observable a on Q pairwise:

    π_j(a)=diag(a(x_j),a(y_j)).

The mass cancels from the commutator,

    [D_j,π_j(a)] =
      [[0,s_j(a(y_j)-a(x_j))],
       [s_j(a(x_j)-a(y_j)),0]].

For a Lipschitz function a, this is bounded uniformly in j. Its norm is

    sup_j |a(x_j)-a(y_j)|/d(x_j,y_j)=Lip(a).

The last equality follows from density of Q and continuity of a and
the metric away from the diagonal. Therefore the Connes distance

    d_D(x,y)=sup_{||[D,π(a)]||≤1} |a(x)-a(y)|

equals d(x,y). The upper bound is the Lipschitz inequality; equality is
attained by a(z)=d(z,y).

Finite two-point commutators, sharp atomic 2^n filtration seminorms,
and the continuous-function logical projection algebra have already
passed the Lean kernel audit in LTR v0.6. The direct-sum domain and
uniform bounded-commutator theorem remain explicit Lean obligations.

## 5. Interfaces with the logic theorem

The original one-axiom nullary first-order theory has completion space
homeomorphic to Cantor space, proved in NullaryTopology.lean. For any
first-order sentence φ its characteristic projection p_φ is a
self-adjoint idempotent in C(X_T,C). The norm of the refutation
projection is 0 iff φ follows semantically from T. Its pullback under
any conservative compact-network projection preserves the norm.
For a syntactic endomorphism σ the exact square

    F_σ* p_φ = p_(σφ)

is already kernel verified. The full metric/spectral realization is
intended to preserve these named logical observables.

Computability is attached to the *effective sentence marking* and
the chosen filtration. The bare homeomorphism type of X_T and an
unmarked Dirac spectrum do not recover the complete syntax.

## 6. Proof status

| Obligation | Status |
|---|---|
| Finite block algebra, square, symmetry | Lean |
| Linear algebraic Dirac operator on Finsupp core | Lean |
| Finite-coordinate density in ℓ² and two-component block core | Lean; CI run 41580342867 |
| Scalar Hilbert block-diagonal maps | Lean |
| Geometric squared-resolvent scalar tail | Lean |
| Finite-rank Hilbert block maps compact | Lean |
| Exact cutoff identity and compact squared resolvent | Lean; CI runs 41580149320, 41580342867 |
| Densely defined maximal-domain unbounded operator | Written argument |
| D closed and self-adjoint | Written argument |
| Compact ordinary resolvent (D-i)^(-1) | Written argument |
| Bounded commutators and Connes distance recovery | Written analytic proof, finite Lean algebra |

Standard precedents: Christensen and Ivan (2007), Sums of
two-dimensional spectral triples; Christensen and Ivan (2006),
Spectral triples for AF C*-algebras and metrics on the Cantor set;
Pearson and Bellissard (2009), Noncommutative Riemannian Geometry
and Diffusion on Ultrametric Cantor Sets. Any novelty claim requires
specialist comparison, especially against computable Gelfand duality.

No theological predicates enter these constructions.
