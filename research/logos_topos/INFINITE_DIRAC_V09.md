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

### Additional complex formalization under CI

`ComplexWeightedDiracRange.lean` contains pointwise energy estimates
\[
\|D_j(w_jv)\|\le\|v\|,\quad
\|D_j^2(w_jv)\|\le\|v\|.
\]
These establish \(R_C(H_C)\subseteq\operatorname{Dom}(D^2)\)
when the full statements pass the Lean audit.

`ComplexSquaredResolventIdentity.lean` defines exact two-sided
equations for \((I+D^2)^{-1}\) with explicit domain witnesses.
`ComplexOrdinaryResolventBlock.lean` contains the complex block
candidate \((D_j-iI)^{-1}\) and its two inverse equations.
Their final status requires passing CI at the actual branch head.

### Ordinary resolvent: classical analytic proof and Lean target

For each complex block,

\[
Q_j = (D_j-iI)^{-1}
    = \frac{D_j+iI}{1+\mu_j^2}.
\]

As \(D_j\) is Hermitian and \(D_j^2=\mu_j^2 I\),

\[
Q_j^*Q_j = \frac{I}{1+\mu_j^2},
\qquad
\|Q_j\|=(1+\mu_j^2)^{-1/2}.
\]

Hence the bounded direct sum \(Q=\bigoplus_jQ_j\) has finite-rank
cutoffs with

\[
\|Q-Q_N\|
\le(1+4^N)^{-1/2}\to0,
\]
and is compact.

Moreover, \(D_jQ_j\) has norm
\(\mu_j/\sqrt{1+\mu_j^2}\le1\).
Thus \(Q(H_C)\subseteq\operatorname{Dom}(D)\),
and the block identities give
\[
(D-iI)Q=I_{H_C},
\quad
Q(D-iI)=I_{\operatorname{Dom}(D)}.
\]

This gives the exact **ordinary compact resolvent**
at \(i\) analytically. Lean still needs the bounded block direct sum,
tail compactness and global domain-correct inverse equations.

### Next stages

Once the ordinary resolvent is formally checked, proceed to
bounded commutators \([D,\pi(a)]\), then the equality of the
commutator seminorm and the Lipschitz seminorm, and finally Connes
distance recovery on the marked Stone completion.

The pure operator results require no theological hypotheses.
Prior art includes Christensen–Ivan and Pearson–Bellissard.
Originality of the effective marked logical reconstruction remains
separately under specialist comparison.
