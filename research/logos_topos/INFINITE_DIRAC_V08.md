# LTR v0.8: self-adjoint infinite Dirac operator with compact squared resolvent

**Status:** Lean kernel-built and dependency-audited on the real Hilbert direct sum.
**PR:** https://github.com/patrickdugan/OntologicalProofs/pull/5
**Final full run:** https://github.com/patrickdugan/OntologicalProofs/actions/runs/41589990567

## 1. Concrete infinite-dimensional construction

Let

\[
H_{\mathbb R}=\ell^2(\mathbb N,\mathbb R^2),
\qquad
D_j=\begin{pmatrix}2^j&s_j\\s_j&-2^j\end{pmatrix},
\qquad
\mu_j^2=4^j+s_j^2.
\]

The sequence \(s_j\in\mathbb R\) is arbitrary. We define the partial linear map
\(D\) on the **maximal** domain

\[
\operatorname{Dom}(D)
=\{\psi\in H_{\mathbb R} : (D_j\psi_j)_j\in H_{\mathbb R}\}.
\]

In Lean, \(H_{\mathbb R}\) is
`lp (fun _ : Nat => EuclideanSpace Real (Fin 2)) 2`;
`maximalDiracPMap` has type \(H_{\mathbb R}\to_\ell H_{\mathbb R}\).
These are actual Hilbert vectors, not a finite-dimensional surrogate.

## 2. Densely defined, closed, and self-adjoint

* `DiracBlockCoreDense.lean`: finite-block truncations approximate all Hilbert vectors.
* `UnboundedDiracPMap.lean`: the maximal domain is a real submodule and the action is linear.
* `UnboundedDiracDense.lean`: the maximal domain is dense.
* `UnboundedDiracClosed.lean`: the graph is an intersection of closed coordinate equalizers.
* `EuclideanDiracAdjoint.lean`: each Euclidean \(2\times 2\) block is self-adjoint.
* `InfiniteDiracSymmetry.lean`: \(D\) is formally symmetric on the entire maximal domain.
* `InfiniteDiracSelfAdjoint.lean`: **`maximalDiracPMap_isSelfAdjoint`** proves \(D^*=D\).

The adjoint-domain argument tests any \(y\in\operatorname{Dom}(D^*)\)
against a single-block vector at index \(j\).
For \(z=D^*y\), it obtains \(z_j=D_jy_j\).
Since \(z\in\ell^2\), the blockwise image \((D_jy_j)_j\) lies in
\(\ell^2\), exactly the maximal-domain condition. Formal symmetry
and equality of domains give self-adjointness.

This proof applies to **arbitrary real mass and scale sequences**.
The chosen exponential masses are used below for compactness.

Self-adjointness CI:
https://github.com/patrickdugan/OntologicalProofs/actions/runs/41588703274

## 3. The compact bounded squared-resolvent operator

Define the positive weights

\[
w_j=\frac{1}{1+4^j+s_j^2},
\qquad (R\psi)_j=w_j\psi_j.
\]

`InfiniteSquaredResolventCompact.lean` proves \(R\) compact as
the operator-norm limit of finite-rank block truncations \(R_N\), with

\[
\lVert R-R_N\rVert\le\frac{1}{1+4^N}\longrightarrow 0.
\]

This is on the same infinite-dimensional real Hilbert space as \(D\).
Compactness CI:
https://github.com/patrickdugan/OntologicalProofs/actions/runs/41580149320

## 4. Kernel-verified identification of R with (I + D²)⁻¹

`EuclideanDiracSquaredResolvent.lean` proves on every Euclidean block

\[
D_j^2=\mu_j^2 I,\qquad
w_jv+D_j^2(w_jv)=v.
\]

`WeightedDiracRange.lean` then establishes the uniform Hilbert
estimates

\[
\lVert D_j(w_jv)\rVert\le\lVert v\rVert,\qquad
\lVert D_j^2(w_jv)\rVert\le\lVert v\rVert.
\]

Consequently, for every \(\psi\in H_{\mathbb R}\), the blockwise
action \(R\psi\) belongs to \(\operatorname{Dom}(D)\), and its
unbounded Dirac image belongs to \(\operatorname{Dom}(D)\) again.
Thus \(R(H_{\mathbb R})\subseteq\operatorname{Dom}(D^2)\).

`InfiniteSquaredResolventIdentity.lean` proves the exact equations

\[
(I+D^2)R\psi=\psi
\quad (\forall\psi\in H_{\mathbb R}),
\]

and

\[
R(I+D^2)\psi=\psi
\quad (\forall\psi\in\operatorname{Dom}(D^2)).
\]

The named theorems are

* `chosenSquaredResolvent_mem_maximalDiracDomain`
* `chosenSquaredResolvent_D_mem_maximalDiracDomain`
* `chosenSquaredResolvent_right_inverse`
* `chosenSquaredResolvent_left_inverse`

The domain conditions are included explicitly in the Lean statements.
These results establish that the already-proved **compact** map \(R\)
is the **two-sided inverse** of the positive unbounded map \(I+D^2\).
The proof uses explicit domain-membership and inverse equations instead
of introducing a separately packaged \(I+D^2\) `LinearPMap` inverse.

Block-inverse CI:
https://github.com/patrickdugan/OntologicalProofs/actions/runs/41589242857

Weighted-range CI:
https://github.com/patrickdugan/OntologicalProofs/actions/runs/41589786713

Full two-sided inverse CI:
https://github.com/patrickdugan/OntologicalProofs/actions/runs/41589990567

## 5. What remains

The standard *complex* spectral triple is a later formalization step.
The present Hilbert-space results are on \(\ell^2(\mathbb N,\mathbb R^2)\).

Remaining Lean tasks:

1. Real-to-complex construction with the ordinary \((D-iI)^{-1}\),
   or a compact-resolvent equivalence established in the chosen formal interface.
2. Infinite direct-sum commutator bounds
   \(\lVert[D,\pi(a)]\rVert=\mathrm{Lip}(a)\).
3. Exact Connes-distance recovery on the marked Stone completion.
4. Spectral \(p\)-summability for every \(p>0\) in Lean.
5. Formal integration of the effective logical marking and
   translation maps with the spectral realization.

The written classical arguments for these later tasks appear in
`INFINITE_DIRAC_V07.md`.

## 6. Interpretive boundary

The mass-shifted two-point direct-sum technique has related precedents
in Christensen–Ivan and Pearson–Bellissard. The results above verify
the concrete analytic construction and its Lean proof obligations.
Novelty of an *effective, marked, logic-to-topology* reconstruction
requires a separate comparison with existing spectral-triple and
computable duality constructions.

No theological assumptions occur in the Lean theorems.
