# LTR-MAN-10: A four-dimensional no-go theorem for the two-bit Hamming metric

**November 2026. Status:** Complete written analytic proof; a Lean matrix certificate remains to be formalized. This note accompanies the numerical dimension-search program in the Logos–Topos spectral geometry research.

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
\boxed{5\le r_{\rm geom}(2)\le8.}
\]

The exact values 5, 6, or 7 remain mathematically unresolved. Numerical searches over these dimensions supply candidates but cannot prove feasibility or impossibility.

The proof is entirely finite-dimensional. Its central components are finite-dimensional projection ranks, the norm of a rank-two star commutator, the Hilbert–Schmidt/operator-norm inequality, the singular values of a \(2\times2\) complex matrix, and the compactness of a finite-dimensional norm ball. This makes it an appropriate next Lean target.

**Potential stronger goal:** derive an obstruction for five or six dimensions using the multiplicities of the four minimal truth projections and the support structure of the two norm-attaining opposite-pair witnesses.

## References within this repository

- `Neoplatonic/LTR/ManifestationOptimalRange.lean`: rank-optimal \(2^m\) truth-only projection
- `Neoplatonic/LTR/BooleanCubeConnesDistance.lean`: edge-block Hamming distance construction, pending Lean CI
- `research/logos_topos/HYPERCUBE_PLAQUETTE_V09.md`: four-dimensional unit square flux law, proved analytically
- `research/logos_topos/HYPERCUBE_SPECTRAL_GEOMETRY_V09.md`: edge-block dimension accounting
