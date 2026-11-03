# LTR v0.10: a kernel-verified complex compact-resolvent Dirac operator

**Authoritative full Lean CI:** https://github.com/patrickdugan/OntologicalProofs/actions/runs/41599306612

**Draft PR:** https://github.com/patrickdugan/OntologicalProofs/pull/5

## 1. The infinite Hilbert-space operator

We use the actual infinite-dimensional complex Hilbert direct sum

\[
H_{\mathbb C}=\ell^2(\mathbb N,\mathbb C^2).
\]

For each \(j\in\mathbb N\), fix an arbitrary real scale \(s_j\).
Define the Hermitian two-point block

\[
D_j=\begin{pmatrix}2^j&s_j\\s_j&-2^j\end{pmatrix},
\qquad
D_j^2=\mu_j^2 I,\quad\mu_j^2=4^j+s_j^2.
\]

The *maximal* blockwise Dirac operator is the complex-linear partial
map \(D\) with

\[
\operatorname{Dom}(D)=
\{\psi\in H_{\mathbb C}:(D_j\psi_j)_j\in H_{\mathbb C}\},
\qquad
(D\psi)_j=D_j\psi_j.
\]

The following declarations are kernel-built and axiom-audited:

- `complexEuclideanDiracBlock_isSelfAdjoint` and
  `complexEuclideanDiracBlock_square`, for the complex block;
- `maximalComplexDiracDomain_dense`, with constructive finite-block
  approximations;
- `maximalComplexDiracPMap_isClosed`, from a coordinatewise closed graph;
- **`maximalComplexDiracPMap_isSelfAdjoint`**, proving \(D^*=D\) by
  identifying the full domain of the Hilbert adjoint.

The self-adjointness theorem holds for *arbitrary real mass and scale
sequences*. The exponential choice \(m_j=2^j\) is used for compactness.

**Self-adjointness CI:**
https://github.com/patrickdugan/OntologicalProofs/actions/runs/41595346041

## 2. The compact squared-resolvent identity

The bounded complex Hilbert operator

\[
(R\psi)_j=w_j\psi_j,
\qquad w_j=\frac{1}{1+4^j+s_j^2}
\]

is a norm limit of finite-rank operators, with

\[
\|R-R_N\|\le \frac{1}{1+4^N}\to 0.
\]

The theorem `chosenComplexSquaredResolvent_isCompact` proves actual
compactness. The domain lemmas put \(R(H_{\mathbb C})\) inside
\(\operatorname{Dom}(D^2)\); the explicit two-sided inverse equations

\[
(I+D^2)R=I_{H_{\mathbb C}},
\qquad
R(I+D^2)=I_{\operatorname{Dom}(D^2)}
\]

are provided by `chosenComplexSquaredResolvent_right_inverse` and
`chosenComplexSquaredResolvent_left_inverse`.

**Squared-resolvent CI:**
https://github.com/patrickdugan/OntologicalProofs/actions/runs/41597215665

## 3. The ordinary resolvent at i

The genuine ordinary resolvent block is

\[
Q_j=(D_j-iI)^{-1}=\frac{D_j+iI}{1+\mu_j^2}.
\]

`complexOrdinaryResolventBlock_right_inverse` and
`complexOrdinaryResolventBlock_left_inverse` verify both exact finite
complex block identities.

The bounded complex-linear direct sum

\[
(Q\psi)_j=Q_j\psi_j
\]

is implemented as `chosenComplexOrdinaryResolventCLM`.
The theorem `chosenComplexOrdinaryResolvent_mem_maximalComplexDiracDomain`
proves \(Q(H_{\mathbb C})\subseteq\operatorname{Dom}(D)\).
The domain-correct inverse equations are

\[
(D-iI)Q=I_{H_{\mathbb C}},
\qquad
Q(D-iI)=I_{\operatorname{Dom}(D)},
\]

verified by `chosenComplexOrdinaryResolvent_right_inverse` and
`chosenComplexOrdinaryResolvent_left_inverse`. Thus \(Q\) is the
actual bounded ordinary resolvent of the self-adjoint unbounded \(D\).

**Global ordinary-resolvent CI:**
https://github.com/patrickdugan/OntologicalProofs/actions/runs/41598388669

## 4. Compactness of the ordinary resolvent

For \(m_j=2^j\), Lean establishes the uniform bound

\[
\boxed{\|Q_j\|\le 2^{1-j}.}
\]

This follows from weighted complex Dirac energy estimates. It remains
valid for *arbitrary* real couplings \(s_j\). The corresponding
declarations include

- `weightedComplexDiracBlock_norm_le_invMass`;
- `complexOrdinaryResolventBlock_norm_le_invPow`;
- `complexOrdinaryResolventBlock_norm_le_tail`.

Each finite-rank truncation \(Q_N\) is a finite sum of operators
factoring through the first \(N\) complex two-dimensional coordinates.
The theorem `finiteComplexOrdinaryResolvent_compact` proves these
operators are compact. Their cutoff identity and norm bound are

\[
Q_N=Q-Q_{\ge N},
\qquad
\boxed{\|Q-Q_N\|\le 2^{1-N}\to0.}
\]

The theorem `chosenComplexOrdinaryResolvent_isCompact` uses
mathlib's norm-closedness of compact operators to conclude

\[
\boxed{\operatorname{IsCompactOperator}((D-iI)^{-1}).}
\]

The bound is deliberately conservative. The sharp analytic estimate
is \(\|Q_j\|=(1+\mu_j^2)^{-1/2}\), whereas the formalized
\(2^{1-j}\) bound already proves compactness.

**Decay CI:**
https://github.com/patrickdugan/OntologicalProofs/actions/runs/41598867428

**Finite-rank cutoff CI:**
https://github.com/patrickdugan/OntologicalProofs/actions/runs/41598961140

**Complete compact ordinary-resolvent theorem and axiom audit:**
https://github.com/patrickdugan/OntologicalProofs/actions/runs/41599306612

## 5. Audit standard and interpretation

`Neoplatonic/LTR/Check.lean` imports all of these declarations, prints
their axiomatic dependencies, and is built by
`.github/workflows/ltr-reconstruction.yml`. The workflow rejects
`sorryAx` and `ofReduceBool`. It also runs the finite
reconstruction Python tests.

This is a formal proof of a **densely defined closed self-adjoint
complex Dirac operator with compact ordinary resolvent** on an actual
infinite Hilbert space. It supplies the analytic operator-theory part
of the proposed spectral realization.

The standard spectral triple still requires:

1. A faithful complex representation of the marked function algebra
   on this Hilbert space, with the required domain invariance.
2. Boundedness and exact norm of the infinite commutators
   \([D,\pi(a)]\) for the chosen Lipschitz algebra.
3. Connes distance recovery for the marked Stone completion.
4. Spectral summability and any desired functorial/effective
   reconstruction properties, expressed as further theorems.

The written analytic arguments and prior stages are in
`INFINITE_DIRAC_V07.md` through `INFINITE_DIRAC_V09.md`.

## 6. Research and originality boundary

Two-point direct-sum spectral constructions have prior art in the
work of Christensen–Ivan and Pearson–Bellissard. This Lean development
checks the specific infinite operator-theory claims, which should be
distinguished from a novelty claim about the effective, syntactically
marked **Logos-to-Topos reconstruction**.

The mathematics here invokes no theological predicates. Its
philosophical interpretation belongs to *Divine Elegance* and is
subject to the further recovery and invariance results above.
