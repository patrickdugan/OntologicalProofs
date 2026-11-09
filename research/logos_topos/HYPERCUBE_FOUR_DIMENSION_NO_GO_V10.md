# LTR-MAN-10: A four-dimensional no-go theorem for the two-bit Hamming metric

**November 2026. Status:** Written analytic four- and five-dimensional no-go arguments. The MAN-12 through MAN-25 Lean sequence verifies the five-dimensional zero-product spectral theorem and the canonical doubled-fibre Connes-dual contradiction with explicit hypotheses. The universal all-representations Lean theorem remains open. See [the formalization ledger](HYPERCUBE_FIVE_DIM_LEAN_LEDGER_V25.md).

## Statement

Let \(A=\mathbb C^4\) be the algebra of complex observables on the four Boolean truth profiles

\[
0=00,\quad 1=01,\quad 2=10,\quad 3=11.
\]

Suppose \(\pi:A\to B(H)\) is a faithful, unital star representation on a **four-dimensional complex Hilbert space** and \(D\) is an arbitrary self-adjoint operator on \(H\). Its Connes pseudometric is

\[
d_D(i,j)=\sup\big\{|f(i)-f(j)|:\,
  \|[D,\pi(f)]\|\le1\big\}.
\]

**Theorem.** The six distances cannot all equal the Hamming distances on the Boolean square. In particular, for a finite-dimensional faithful spectral realization with *exact* Hamming distances,

\[
\boxed{\dim_\mathbb C H\ge5.}
\]

This theorem allows **arbitrary complex Hermitian Dirac matrices**, including opposite-corner couplings. It goes beyond the special four-edge, unit-modulus plaquette analysis.

## Step 1: reduce the representation

A faithful unital representation of \(\mathbb C^4\) on \(\mathbb C^4\) sends the four atomic idempotents to nonzero pairwise orthogonal projections summing to one. Since their ranks are positive integers summing to four, all four have rank one. Choose a unitary basis so that

\[
\pi(f)=\operatorname{diag}(f_0,f_1,f_2,f_3).
\]

Write \(D=(d_{ij})\) as an arbitrary Hermitian \(4\times4\) matrix. The diagonal entries cancel in commutators, so only the six independent off-diagonal entries matter.

Set

\[
S=|d_{01}|^2+|d_{02}|^2+|d_{13}|^2+|d_{23}|^2,
\qquad
\alpha=|d_{03}|^2,\quad\beta=|d_{12}|^2.
\]

\(S\) is the total squared coupling weight on square edges. \(\alpha,\beta\) are squared couplings across opposite vertices.

## Step 2: vertex indicators force a Frobenius lower bound

For the indicator function \(\delta_i\) of vertex \(i\),

\[
\|[D,\pi(\delta_i)]\|
=\left(\sum_{j\ne i}|d_{ij}|^2\right)^{1/2}.
\]

This follows by writing the commutator as the skew-Hermitian rank-two block matrix with its only nonzero row and column at vertex \(i\).

If the Connes metric equals Hamming, every vertex has an adjacent vertex at distance one. Therefore

\[
1=|\delta_i(i)-\delta_i(j)|\le
d_D(i,j)\,\|[D,\pi(\delta_i)]\|
=\|[D,\pi(\delta_i)]\|.
\]

Squaring and summing these four inequalities counts each squared off-diagonal Dirac entry twice, yielding

\[
\boxed{S+\alpha+\beta\ge2.}\tag{1}
\]

## Step 3: opposite-corner witnesses give two upper bounds

Because the desired metric is finite, the commutator seminorm has constants as its entire kernel. Its unit ball, modulo constants, is compact in the finite-dimensional real space of self-adjoint functions. Thus the two opposite distances, both equal to two, attain their suprema.

Rotate and translate an attaining observable to take values 0 and 2 at an opposite pair, and take its real part; this preserves the opposite difference and weakens the commutator norm. The two Hamming-one paths between the opposite corners then force midpoint value 1 at each of the remaining vertices, by equality in the triangle inequality.

Consequently both real-valued functions

\[
g=(0,1,1,2),\qquad h=(1,0,2,1)
\]

have commutator operator norm **at most one**.

For any \(4\times4\) matrix \(K\),

\[
\|K\|_F^2\le4\|K\|_{\mathrm{op}}^2.
\]

For \(K=[D,\pi(g)]\), all four square edges have truth-value difference one, the \(0\leftrightarrow3\) coupling has difference two, and the \(1\leftrightarrow2\) coupling has difference zero. Therefore

\[
\|[D,\pi(g)]\|_F^2=2(S+4\alpha)\le4
\quad\Rightarrow\quad
\boxed{S+4\alpha\le2.}\tag{2}
\]

Likewise \(h\) gives

\[
\boxed{S+4\beta\le2.}\tag{3}
\]

Averaging (2) and (3) gives \(S+2(\alpha+\beta)\le2\). Combining with (1),

\[
0\le\alpha+\beta\le0.
\]

Hence

\[
\boxed{\alpha=\beta=0,\qquad S=2.}\tag{4}
\]

The desired distances have forced *both* opposite-corner Dirac couplings to vanish.

## Step 4: the square coupling matrix must be unitary

Order the even-parity vertices \((0,3)\) before the odd-parity vertices \((1,2)\). The only remaining nonzero off-diagonal part of \(D\) is encoded by

\[
X=
\begin{pmatrix}
d_{01}&d_{02}\\
d_{31}&d_{32}
\end{pmatrix}.
\]

For \(g=(0,1,1,2)\), the commutator is, up to harmless diagonal signs, a skew-adjoint block matrix whose operator norm equals \(\|X\|_{\mathrm{op}}\). As \(\|[D,\pi(g)]\|\le1\),

\[
\|X\|_{\mathrm{op}}\le1.
\]

But \(\|X\|_F^2=S=2\). Both squared singular values are at most one and sum to two, so both equal one. Thus **\(X\) is unitary**.

The modulus relations of a \(2\times2\) unitary give

\[
|d_{01}|=|d_{32}|=:a,\quad
|d_{02}|=|d_{31}|=:b,\qquad
a^2+b^2=1.
\]

## Step 5: the coordinate observables contradict unitarity

Consider the two truth-coordinate functions

\[
p=(0,1,0,1),\qquad q=(0,0,1,1).
\]

Because the opposite couplings have vanished, \([D,\pi(p)]\) consists of two disjoint two-point blocks corresponding to the \(0\!\!\leftrightarrow\!\!1\) and \(2\!\!\leftrightarrow\!\!3\) edges. Hence

\[
\|[D,\pi(p)]\|=a.
\]

Similarly, \(\|[D,\pi(q)]\|=b\).

Each coordinate function separates adjacent vertices by exactly one, and every adjacent Connes distance is assumed equal to one. The dual definition of distance therefore requires

\[
a\ge1,\qquad b\ge1.
\]

This contradicts \(a^2+b^2=1\). The four-dimensional faithful spectral realization is impossible.

\[
\boxed{r_{\rm geom}(2)\ge5.}
\]

## Implications

The eight-dimensional independent-edge construction of LTR-MAN-09 is an explicit realization, so the rigorous present bounds are

\[
\boxed{6\le r_{\rm geom}(2)\le8.}
\]

The precise minimum among dimensions 6, 7 and 8 remains unresolved under the written lower-bound argument. Numerical searches in six and seven dimensions supply candidates but cannot prove feasibility or impossibility.

The proof is entirely finite-dimensional. Its central components are finite-dimensional projection ranks, the norm of a rank-two star commutator, the Hilbert–Schmidt/operator-norm inequality, the singular values of a \(2\times2\) complex matrix, and the compactness of a finite-dimensional norm ball. This makes it an appropriate next Lean target.

**Potential stronger goal:** derive an obstruction for five or six dimensions using the multiplicities of the four minimal truth projections and the support structure of the two norm-attaining opposite-pair witnesses.

## References within this repository

- `Neoplatonic/LTR/ManifestationOptimalRange.lean`: rank-optimal \(2^m\) truth-only projection
- `Neoplatonic/LTR/BooleanCubeConnesDistance.lean`: edge-block Hamming distance construction, pending Lean CI
- `research/logos_topos/HYPERCUBE_PLAQUETTE_V09.md`: four-dimensional unit square flux law, proved analytically
- `research/logos_topos/HYPERCUBE_SPECTRAL_GEOMETRY_V09.md`: edge-block dimension accounting


## Extension: five-dimensional no-go by extremal spectral supports

**Theorem (written analytic proof).** In fact, a faithful unital representation
of the two-bit truth algebra with exact Hamming Connes metric requires

\[
\boxed{\dim_{\mathbb C}H\ge6.}
\]

### Two opposite-distance witnesses constrain both coordinate commutators

Let \(P,Q\) be the commuting atomic-coordinate projections for the first
and second Boolean bits. Set

\[
A=i[D,P],\qquad B=i[D,Q].
\]

These are Hermitian, trace-zero matrices. Each anticommutes with its
corresponding grading \(2P-I\) or \(2Q-I\). Their nonzero eigenvalues
therefore occur in pairs \(\lambda,-\lambda\), with matching
multiplicities.

The two opposite-corner distance witnesses \(p+q\) and \(p-q\)
established in Step 3 imply

\[
\|A+B\|\le1,\qquad \|A-B\|\le1.
\]

Each coordinate function separates a Hamming-one pair, so exact
adjacent distances also imply \(\|A\|\ge1\) and \(\|B\|\ge1\).
The triangle inequality applied to \((A+B)\pm(A-B)\) gives the
reverse inequalities. Consequently

\[
\boxed{\|A\|=\|B\|=1.}
\]

Let \(E_A\) be the sum of the \(+1\) and \(-1\) eigenspaces of
\(A\). Spectral symmetry implies \(\dim E_A\ge2\), with
equal \(+1\) and \(-1\) multiplicities. For a unit eigenvector
\(v\in E_A\), we have \(\|Av\|=1\). The two contractions give

\[
\|(A+B)v\|^2\le1,\qquad
\|(A-B)v\|^2\le1.
\]

Adding and applying the parallelogram identity yields

\[
2(\|Av\|^2+\|Bv\|^2)\le2,
\quad\text{so}\quad Bv=0.
\]

Thus \(E_A\subseteq\ker B\). By symmetry,
\(E_B\subseteq\ker A\), where \(E_B\) consists of the
\(\pm1\) eigenspaces of \(B\). Self-adjointness implies
\(E_A\perp E_B\). Both have dimension at least two.

If \(\dim H\le5\), write the reducing orthogonal decomposition

\[
H=E_A\oplus E_B\oplus R,\qquad \dim R\le1.
\]

The trace of \(A\) on \(E_A\) is zero by the pairing of
\(+1\) and \(-1\) eigenvalues, while \(A\) vanishes on
\(E_B\). Since \(\operatorname{tr}A=0\), it must also vanish
on the at-most-one-dimensional reducing complement \(R\).
Similarly, \(B\) vanishes on \(R\) and on \(E_A\).

Therefore

\[
\boxed{AB=BA=0\qquad\text{when }\dim H\le5.}\tag{5}
\]

### Vanishing product forces a disconnected square

Let the four minimal projections of \(\pi(\mathbb C^4)\) have
positive multiplicities \(n_0,\ldots,n_3\). At dimension at most
five, at most one multiplicity can exceed one.

Inspect the \((0,0)\) block of \(AB\). Because one of the bit
differences vanishes across each square edge, the only possible
contribution is the two-bit-flipping coupling \(0\leftrightarrow3\).
Up to a nonzero sign, the block equals
\(D_{03}D_{03}^*\). Equation (5) forces \(D_{03}=0\).
The \((1,1)\) block similarly gives \(D_{12}=0\).

All surviving intervertex couplings now lie on the four Hamming-one
edges. Form the support graph whose vertices are \(0,1,2,3\), with
edge \(u-v\) present when the corresponding coupling block
\(D_{uv}\) is nonzero.

Suppose vertex \(v\) has a one-dimensional Hilbert fibre and both
of its incident square-edge couplings are nonzero. Let \(u\) be
its neighbor in the first-bit direction and \(w\) its neighbor
in the second-bit direction. The \((u,w)\) block of \(AB\)
contains precisely the ordered two-edge path \(u-v-w\).
Its contribution is a nonzero scalar times

\[
D_{uv}D_{vw}:H_w\longrightarrow H_u.
\]

Because \(H_v\) has dimension one, the composition of two nonzero
maps through \(H_v\) is nonzero. The alternative two-edge path
has the wrong order of bit directions and contributes zero.
This contradicts \(AB=0\). Hence every one-dimensional fibre
has **at most one** incident nonzero square edge.

The support graph must be connected: otherwise a function constant
on each graph component but unequal between two components has zero
Dirac commutator and makes the Connes distance infinite.

Yet a connected spanning subgraph of a square requires at least
three edges and therefore total degree at least six. With at most
one fibre of multiplicity greater than one, and all other vertices
restricted to degree at most one, the total possible degree is at
most \(2+1+1+1=5\). Contradiction.

Thus a faithful exact-Hamming representation in dimension five
cannot exist. Together with the earlier dimension-four argument
and the verified rank-four truth-algebra lower bound,

\[
\boxed{6\le r_{\mathrm{geom}}(2)\le8.}
\]

The extension uses the operator-norm parallelogram identity,
spectral pairing of the commutator with a projection,
finite-dimensional trace, and multiplication of rectangular
coupling blocks. The formal Lean obligation is to encode the
\(AB=0\) support lemma and the four-vertex graph degree argument.

The dimension-six and dimension-seven cases remain open.
