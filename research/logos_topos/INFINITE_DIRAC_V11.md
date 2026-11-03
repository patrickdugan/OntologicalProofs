# LTR v0.11: verified observable representation and dense marked metric core

**Status:** Bounded complex Hilbert observable representation, its domain-correct commutator and faithfulness, plus the numerical dense-marked metric theorem, all Lean kernel-built and axiom-audited.

**Full audit:** https://github.com/patrickdugan/OntologicalProofs/actions/runs/41607111079

**Draft pull request:** https://github.com/patrickdugan/OntologicalProofs/pull/5

## 1. Relation to v0.10

The previous stage established a genuine densely defined, closed,
self-adjoint complex operator on
\[
H=\ell^2(\mathbb N,\mathbb C^2),\quad
D_j=\begin{pmatrix}2^j&s_j\\s_j&-2^j\end{pmatrix}
\]
with maximal square-summable domain, and a **compact ordinary resolvent**
\((D-iI)^{-1}\) with finite-rank truncation error at most \(2^{1-N}\).
Those kernel-verified results remain included in the v0.11 audit.
The v0.10 ledger is `INFINITE_DIRAC_V10.md`.

## 2. Verified two-point observable algebra

For two real values \(a,b\), the complex Euclidean block is
\[
\pi_j(a,b)=\begin{pmatrix}a&0\\0&b\end{pmatrix}.
\]
`ComplexObservableBlocks.lean` proves matrix Hermitianity, unit,
multiplicativity, and exact mass-independent commutator:
\[
[D_j,\pi_j(a,b)] =
\begin{pmatrix}0&s_j(b-a)\\s_j(a-b)&0\end{pmatrix}.
\]

`ComplexObservableNorm.lean` identifies that block commutator as
\(s_j(b-a)J\), with \(J=\left[\begin{smallmatrix}0&1\\-1&0\end{smallmatrix}\right]\)
a unitary complex-linear rotation. Consequently the block
operator norm is exactly \(|s_j(b-a)|\).

## 3. Verified bounded representation and domain invariance

Given real-valued sequences \((a_j,b_j)\) bounded in absolute value
by some common \(M\), `ComplexObservableRepresentation.lean`
defines an actual bounded complex-linear operator \(\pi(a)\) on
\(H\) by coordinatewise multiplication with the above diagonal
matrices. It has operator norm at most \(M\), maps products
correctly on blocks, and sends the unit observable to the identity.

Given in addition a finite common edge-gradient bound
\[
|s_j(b_j-a_j)|\le L\qquad\text{for every }j,
\]
`ComplexObservableCommutator.lean` constructs a bounded complex
Hilbert operator \(C_a\) with \(\|C_a\|\le L\) and proves:
\[
\pi(a)\operatorname{Dom}(D)\subseteq\operatorname{Dom}(D),
\qquad
D\pi(a)\psi-\pi(a)D\psi=C_a\psi
\quad(\psi\in\operatorname{Dom}(D)).
\]

These statements use the actual unbounded maximal-domain Dirac map,
including the domain-membership witnesses. The infinite operator's
commutator is therefore bounded for the stated observables.

## 4. Verified faithfulness to dense continuous real observations

`ComplexObservableFaithful.lean` proves that a single diagonal block
vanishes exactly when both real endpoint values vanish. If the
bounded direct-sum representation vanishes, all marked endpoint
values vanish.

`ComplexDenseObservableFaithful.lean` then proves: for a continuous
real \(a:X\to\mathbb R\), if \(q:\mathbb N\to X\) has dense range
and every sampled \(q(n)\) appears as a marked endpoint, vanishing
of the bounded Hilbert representation forces \(a=0\) everywhere.

This is faithfulness for explicitly represented real continuous
observables; a bundled complex \(C(X)\) star-algebra homomorphism
remains a further formal construction.

## 5. Verified metric recovery from dense marked edge gradients

Let \(X\) be a metric space with a countable dense sequence \(q_n\).
Suppose the edge enumeration \((x_j,y_j)\) lists distinct endpoints
and covers every ordered pair of distinct values from \(q\).
Choose \(s_j=d(x_j,y_j)^{-1}\).

`ComplexMarkedMetric.lean` proves the edge quotient identity
\[
|s_j(a(y_j)-a(x_j))|
=\frac{|a(y_j)-a(x_j)|}{d(x_j,y_j)}.
\]

`ComplexDenseMarkedMetric.lean` uses continuity and density to prove
for every continuous real \(a\):
\[
\bigl(\forall j:\ |s_j(a(y_j)-a(x_j))|\le1\bigr)
\ \Longleftrightarrow\bigl(\forall x,y\in X:\ |a(x)-a(y)|\le d(x,y)\bigr).
\]

It also proves the dual metric witness: the upper bound holds
for every admissible continuous real observable, with equality
attained by \(a(z)=d(z,y)\).

These results apply to potentially uncountable compact metric
spaces provided the dense-sequence and edge-marking hypotheses
are supplied.

## 6. Explicit pending norm and Connes-distance obligations

The following new source modules are **staged but excluded** from
the successful kernel/axiom audit:

- `ComplexObservableSeminorm.lean`: each block commutator norm
  should be bounded by the global Hilbert commutator norm, yielding
  the optimal uniform marked gradient bound;
- `ComplexMarkedCommutatorCriterion.lean` and
  `ComplexDenseMarkedCommutatorCriterion.lean`: the norm-one
  Hilbert commutator ball should coincide with the Lipschitz ball;
- `ComplexDenseConnesDistance.lean`: equality of the actual
  operator-norm Connes-style distance with the metric of the
  dense-marked completion.

The bottleneck is Lean elaboration of the single-coordinate
Hilbert norm lower bound in `ComplexObservableSeminorm.lean`.
An abstract coordinatewise-operator proof is staged.
The corresponding mathematical assertion is elementary but its
full Lean kernel verification is **pending**. The resulting metric
claim is consequently verified in numerical marked-gradient form
at present, not yet as a complete operator-defined Connes distance.

## 7. Further reconstruction boundaries

A standard spectrally represented complex function algebra still
needs a bundled faithful \(C(X,\mathbb C)\) star-algebra homomorphism,
uniform-boundedness witnesses for all continuous functions on
compact \(X\), and the selection of its Lipschitz subalgebra.
The particular logical Stone space, its effective sentence labels,
the existence/choice of a compatible dense marking, and
interpretation-functorial properties also need explicit connection.

No theological premises are used in these Lean constructions.
The two-point spectral approach has significant precedents in
Christensen–Ivan and Pearson–Bellissard. The original research
question concerns the *effective marked logical reconstruction*,
not the existence of two-point spectral triples alone.

## 8. Verification

The v0.11 audit is driven by
`Neoplatonic/LTR/Check.lean` and
`.github/workflows/ltr-reconstruction.yml`.
It checks 318 named theorem dependencies, rejects `sorryAx`
and `ofReduceBool`, and runs finite Python reconstruction tests.

**Successful run:**
https://github.com/patrickdugan/OntologicalProofs/actions/runs/41607111079

The PR remains draft and unmerged.
