# LTR-MAN-09: Hypercube spectral geometry and the cost of retaining distance

**Status:** November 4, 2026. Formal Lean statements have been staged in PR #31. Do not describe new declarations as kernel-verified until CI passes.

## 1. Source logic and its finite Stone space

For the independent nullary predicates \(p_0,\ldots,p_{m-1}\), the space of truth profiles is

\[
V_m=\{0,1\}^m,\qquad |V_m|=2^m.
\]

The associated finite complex observable algebra is \(A_m=C(V_m,\mathbb C)\), isomorphic to \(\mathbb C^{2^m}\).

LTR-MAN-08 has already established an exact rank-\(2^m\) compression of the actual infinite Hilbert representation of the nullary Stone space. On that subspace the observables are scalar-diagonal, and the compressed Dirac from independently selected scalar coordinates is diagonal, so its commutators with this algebra vanish. To encode distance we need off-diagonal couplings.

## 2. A unique index for each undirected hypercube edge

An edge is specified by a coordinate \(i\in\{0,\ldots,m-1\}\) and a vertex \(u\) with \(u_i=0\). It joins

\[
u \longleftrightarrow u^{(i)},\quad
u^{(i)}_i=1,\quad u^{(i)}_j=u_j\;(j\ne i).
\]

Every undirected Hamming-one pair appears exactly once. For \(m\ge1\),

\[
|E_m|=m2^{m-1}.
\]

For \(m=0\), there is one vertex and no edge.

The Lean type is

```lean
abbrev BooleanCubeVertex (m : ℕ) := Fin m → Bool

abbrev BooleanCubeEdge (m : ℕ) :=
  Σ i : Fin m, {u : BooleanCubeVertex m // u i = false}
```

For \(m=n+1\), fixing a bit to false gives an equivalence with \(\{0,1\}^n\), so the edge count is \((n+1)2^n\).

## 3. Finite edge Hilbert representation

Give every edge \(e=(u,v)\) its own copy of \(\mathbb C^2\):

\[
H_m^{\rm edge}=\bigoplus_{e\in E_m}\mathbb C^2.
\]

For \(m\ge1\),

\[
\boxed{\dim_{\mathbb C} H_m^{\rm edge}=2|E_m|=m2^m.}
\]

Use the genuine self-adjoint two-point operator

\[
D_e=\begin{pmatrix}0&1\\1&0\end{pmatrix},
\qquad
\pi_e(f)=\begin{pmatrix}f(u)&0\\0&f(v)\end{pmatrix}.
\]

Their finite direct sum gives \(D_m=\bigoplus_eD_e\) and \(\pi_m(f)=\bigoplus_e\pi_e(f)\). All operators are bounded, and every resolvent is compact because the Hilbert space is finite-dimensional.

Their commutator is

\[
[D_e,\pi_e(f)] =
\begin{pmatrix}0&f(v)-f(u)\\f(u)-f(v)&0\end{pmatrix},
\]

with exact norm

\[
\|[D_e,\pi_e(f)]\|=|f(v)-f(u)|.
\]

Norms of orthogonal block sums are the maxima of the block norms. Consequently,

\[
\boxed{L_m(f)=\|[D_m,\pi_m(f)]\|
=\max_{\{u,v\}\in E_m}|f(u)-f(v)|.}
\]

For \(m\ge1\), every truth profile is incident to some edge, so the representation is faithful and unital. In dimension zero, the edge Hilbert sum is the zero space: supply a separate one-dimensional scalar block to obtain a faithful unital finite triple there.

## 4. Exact Connes distance equals Hamming distance

For vertices \(x,y\), define

\[
d_{D_m}(x,y)
=\sup\{|f(x)-f(y)|:f\in C(V_m,\mathbb C),\ L_m(f)\le1\}.
\]

Every pair \(x,y\) can be connected by a path flipping precisely the coordinates on which their bit strings disagree. That path has length \(d_H(x,y)\). Since \(L_m(f)\le1\) bounds the change on each unit edge,

\[
|f(x)-f(y)|\le d_H(x,y).
\]

For equality, choose the distance-to-\(y\) function

\[
f_y(z)=d_H(z,y)\in\mathbb R\subset\mathbb C.
\]

The triangle inequality for Hamming distance gives \(L_m(f_y)\le1\), and

\[
|f_y(x)-f_y(y)|=d_H(x,y).
\]

Thus

\[
\boxed{d_{D_m}(x,y)=d_H(x,y).}
\]

This is an exact finite spectral-geometric realization of the metric induced by one-proposition changes.

The Lean work expresses this as a universal upper bound on all unit-commutator functions together with a norm-attaining witness, avoiding a separately bundled \(sSup\) object.

## 5. How much does the extra geometry cost?

| m | Truth-only minimal Hilbert dimension | Undirected edges | Truth + Hamming metric construction dimension |
|---:|---:|---:|---:|
| 1 | 2 | 1 | 2 |
| 2 | 4 | 4 | 8 |
| 3 | 8 | 12 | 24 |
| 4 | 16 | 32 | 64 |
| 5 | 32 | 80 | 160 |
| 6 | 64 | 192 | 384 |
| 8 | 256 | 1,024 | 2,048 |
| 10 | 1,024 | 5,120 | 10,240 |
| 12 | 4,096 | 24,576 | 49,152 |

For the independent m-generator Boolean algebra, rank-\(2^m\) faithful multiplication is achieved by MAN-08. Our edge-block metric construction costs a multiplicative factor of \(m\).

### Conditional optimality for independent edge-block witnesses

Within the class of **orthogonal direct sums of two-point blocks, one block per selected graph edge**, retaining every individual edge difference is necessary to reproduce \(L_m\) for all observables.

To see this, remove one edge \(e=\{u,v\}\) and define the three-level function

\[
g_e(z)=\begin{cases}
0,&z=u,\\
2,&z=v,\\
1,&\text{otherwise}.
\end{cases}
\]

The omitted edge has difference two. Every other hypercube edge has difference at most one because only \(e\) joins the unique zero-valued and two-valued vertices.

Consequently the restricted edge maximum is at most one while the full edge maximum is at least two. Every edge is independently necessary for **exact recovery of the entire edge seminorm** by such an edge-block sum.

Therefore \(m2^m\) is the exact minimum dimension **in this independent two-dimensional edge-block architecture**. This is not a universal Hilbert-dimension lower bound for all finite spectral triples; coupled representations can share Hilbert coordinates between edges, and their capacity remains open.

## 6. Relation to constrained logical theories

If a theory admits a proper subset \(S\subseteq\{0,1\}^m\), its intrinsic truth-observation capacity is \(|S|\), as established by LTR-MAN-06.

Let \(E(S)\) be the induced Hamming-one edge set and \(I(S)\) the set of isolated allowed vertices. An edge-block faithful representation can use

\[
\dim H_S=2|E(S)|+|I(S)|.
\]

One scalar block is required for each isolated vertex to keep the representation faithful. Its seminorm recovers the shortest-path metric on connected components of the induced graph, with unbounded dual distances between disconnected components. That metric may exceed the ambient Hamming distance when constraints remove intermediate profiles.

If the goal is to retain the restricted *ambient* Hamming metric on arbitrary \(S\), additional weighted edges must be selected. The optimization problem becomes a graph-spanner or metric-realization problem rather than edge enumeration alone.

## 7. Formalization ledger

- `BooleanCubeEdges.lean`: unique-edge indexing, Hamming-one property, exact local Hilbert commutator.
- `BooleanCubeGlobal.lean`: finite-edge Hilbert \(\ell^2\) sum, genuine Dirac and observable maps, exact commutator identity, norm as maximum edge gradient.
- `BooleanCubeCapacity.lean`: fixed-bit equivalence, \(m2^{m-1}\) unoriented edge count, and \(m2^m\) scalar coordinate count.
- `BooleanCubeHamming.lean`: one-coordinate repair decreases Hamming distance by one, and unit-step Lipschitz bounds imply global Hamming Lipschitz estimates.
- `BooleanCubeUnitPairs.lean`: every Hamming-one pair occurs as an indexed edge, and a unit Dirac commutator controls Hamming distance.
- `BooleanCubeConnesDistance.lean`: distance-to-vertex attaining functions and exact Connes-distance theorem as upper bound plus witness.

**Verification gate:** inspect the PR's full Lean CI and axiom report. Only merge verified declarations. If the runner is queued, retain the branch and describe results as staged.

## 8. Next conjecture: metric capacity beyond edge blocks

Define

\[
r_{\rm geom}(m)=\min\{\dim_{\mathbb C}H:
(A_m,H,\pi,D)\text{ is finite, faithful and recovers }d_H
\text{ by Connes distance}\}.
\]

The currently constructed edge-block model gives, for \(m\ge1\),

\[
2^m\le r_{\rm geom}(m)\le m2^m.
\]

The lower bound follows because a faithful representation of \(A_m\cong\mathbb C^{2^m}\) requires \(2^m\) nonzero mutually orthogonal minimal projections. The upper bound is the edge sum described above.

For \(m=1\), the bounds coincide, giving \(r_{\rm geom}(1)=2\). For larger \(m\), we can investigate edge sharing and cancellations in non-block-diagonal Dirac matrices, at the cost of computing the global operator norm of the commutator.

A promising mathematical gym would search over self-adjoint \(D\in M_{2^m}(\mathbb C)\) for \(m=2,3\), with a fixed faithful diagonal \(\pi\). Score the resulting Connes distances against Hamming distance and penalize degree of freedom count. A successful equality would show that the blockwise \(m\)-fold overhead is avoidable in a more expressive Dirac geometry.
