# LTR v0.9: complex self-adjoint Dirac and compact squared-resolvent bridge

## Verification snapshot (2026-11-03)

This document distinguishes kernel-verified facts from code awaiting CI and
from a complete but still-unformalized classical analytic argument.

### Kernel-verified complex Hilbert operator

Work on the genuine infinite-dimensional complex Hilbert space

```
H_C := lp (fun _ : Nat => EuclideanSpace Complex (Fin 2)) 2
```

For arbitrary real mass and scale sequences, each two-component block is
the Hermitian matrix

\[
D_j = \begin{pmatrix}m_j&s_j\\s_j&-m_j\end{pmatrix},
\qquad D_j^2=(m_j^2+s_j^2)I.
\]

**Verified:** `ComplexDiracBlock.lean`, including the Hermitian matrix
identity and the self-adjoint complex-linear Euclidean map.
CI: https://github.com/patrickdugan/OntologicalProofs/actions/runs/41595060682

On the maximal square-summable domain

\[
\operatorname{Dom}(D)=
\{\psi\in H_C:(D_j\psi_j)_j\in H_C\},
\]

the complex partial linear map is densely defined, closed and
**self-adjoint**. The adjoint-domain proof tests against every
single-block vector, identifies the adjoint's coordinates with
\(D_j\psi_j\), and invokes their square summability to recover the
maximal domain.

**Verified:** `ComplexDiracDomain.lean`,
`ComplexDiracClosed.lean` and
`ComplexDiracSelfAdjoint.lean`.
The theorem `maximalComplexDiracPMap_isSelfAdjoint` is valid for
arbitrary real sequences \(m_j,s_j\).
CI: https://github.com/patrickdugan/OntologicalProofs/actions/runs/41595346041

### Kernel-verified compact complex bounded operator

Set \(m_j=2^j\), and for arbitrary real \(s_j\), write

\[
\mu_j^2=4^j+s_j^2,\qquad
w_j=(1+\mu_j^2)^{-1}.
\]

Define \(R_C\) as the complex-linear diagonal multiplication operator
\((R_C\psi)_j=w_j\psi_j\).
The finite-rank cutoff \(R_{C,N}\) has exact norm error bounded by

\[
\|R_C-R_{C,N}\|\le (1+4^N)^{-1}\to0.
\]

Therefore \(R_C\) is compact on the actual infinite complex Hilbert
space. The proof uses finite-dimensional compact coordinate maps,
finite sums and norm closure of compact continuous linear maps.

**Verified:** `ComplexSquaredResolventCompact.lean`,
`chosenComplexSquaredResolvent_isCompact`.
CI: https://github.com/patrickdugan/OntologicalProofs/actions/runs/41595551235

### Kernel-verified compact squared resolvent of the maximal complex D

`ComplexWeightedDiracRange.lean` proves the energy estimates

\[
\|D_j(w_jv)\|\le\|v\|,\qquad \|D_j^2(w_jv)\|\le\|v\|.
\]

It follows that \(R_C(H_C)\subseteq\operatorname{Dom}(D^2)\).
`ComplexSquaredResolventIdentity.lean` then verifies the equations
\((I+D^2)R_C=I_H\) and
\(R_C(I+D^2)=I_{\operatorname{Dom}(D^2)}\),
with all unbounded applications explicitly guarded by Lean domain proofs.
Thus the previously proved compact \(R_C\) is exactly
\((I+D^2)^{-1}\) in the partial-operator sense.

**Verified:** `chosenComplexSquaredResolvent_D_mem_maximalComplexDiracDomain`,
`chosenComplexSquaredResolvent_right_inverse` and
`chosenComplexSquaredResolvent_left_inverse`.
CI: https://github.com/patrickdugan/OntologicalProofs/actions/runs/41597215665

### Kernel-verified ordinary compact resolvent at i

For each complex block,

\[
Q_j=(D_j-iI)^{-1}=\frac{D_j+iI}{1+\mu_j^2}.
\]

`ComplexOrdinaryResolventBlock.lean` verifies both finite-dimensional
inverse equations. `ComplexOrdinaryResolventGlobal.lean` constructs a
bounded complex-linear map \(Q=\bigoplus_j Q_j\) on the *infinite*
Hilbert space. It proves
\(Q(H_C)\subseteq\operatorname{Dom}(D)\) and the exact equations

\[
(D-iI)Q\psi=\psi\quad(\psi\in H_C),\qquad
Q(D-iI)\psi=\psi\quad(\psi\in\operatorname{Dom}(D)).
\]

**Verified:** `chosenComplexOrdinaryResolvent_right_inverse`,
`chosenComplexOrdinaryResolvent_left_inverse`.
CI: https://github.com/patrickdugan/OntologicalProofs/actions/runs/41598681662

`ComplexOrdinaryResolventDecay.lean` proves for all \(j\ge N\)
and arbitrary real scales \(s_j\) that

\[
\|Q_j\|\le \frac{2}{2^j}\le\frac{2}{2^N}.
\]

`ComplexOrdinaryResolventFiniteRank.lean` defines the first-\(N\)-block
cutoff \(Q_N\) as a sum of compact finite-dimensional coordinate
operators. `ComplexOrdinaryResolventCompact.lean` establishes their
exact cutoff identity and operator-norm error bound

\[
\boxed{\|Q-Q_N\|\le\frac{2}{2^N}\longrightarrow0}.
\]

The norm-closedness theorem for compact operators now yields

\[
\boxed{\operatorname{IsCompactOperator} Q},\qquad
Q=(D-iI)^{-1}.
\]

**Verified:** `chosenComplexOrdinaryResolvent_isCompact`.
Full kernel build and axiom audit:
https://github.com/patrickdugan/OntologicalProofs/actions/runs/41599306612

The classical sharp block norm is
\(\|Q_j\|=(1+\mu_j^2)^{-1/2}\); the Lean proof uses the coarser
explicit bound \(2/2^j\), sufficient for compactness. This distinction
matters when recording which quantitative statements are formalized.

### Next stages

Once the ordinary resolvent is formally checked, proceed to
bounded commutators \([D,\pi(a)]\), then the equality of the
commutator seminorm and the Lipschitz seminorm, and finally Connes
distance recovery on the marked Stone completion.

The pure operator results require no theological hypotheses.
Prior art includes Christensen–Ivan and Pearson–Bellissard.
Originality of the effective marked logical reconstruction remains
separately under specialist comparison.
