# LTR-MAN-09: A two-bit spectral plaquette and the phase of the Dirac operator

**Status:** Analytical four-state calculation, plus reproducible numerical gym.
The general hypercube Lean formalization is staged in PR #31 pending CI.

## 1. Same logical states, same graph, different spectral metric

Let the truth states of two independent predicates be

\[
00,\ 01,\ 10,\ 11.
\]

Use the faithful minimal four-dimensional representation of
\(C(\{0,1\}^2,\mathbb C)\) as diagonal \(4\times4\) matrices.
The Hamming-one edges form a square. Let \(D_+\) be the Hermitian
adjacency matrix with weight \(+1\) on all four edges.

Let \(D_\pi\) have the same unit-modulus edges, but place a \(-1\)
on the \(10\leftrightarrow11\) edge. The product of edge phases
around the plaquette is respectively \(+1\) and \(-1\).

The distance function associated with a finite Dirac operator is

\[
d_D(x,y)=\sup\{|f(x)-f(y)|:\|[D,\operatorname{diag}(f)]\|\le1\}.
\]

It is sufficient to optimize over real-valued f. For any complex f,
rotating the phase of f(x)-f(y) and taking the real part preserves
the target absolute difference and cannot increase the commutator
operator norm, by the triangle inequality and the involution.

## 2. Exact opposite-vertex distances

Reorder the four vertices as even parity \((00,11)\) followed by
odd parity \((01,10)\), and normalize
\(f(00)=a=0\), \(f(11)=d=1\). Let
\(b=f(01)\), \(c=f(10)\).

The commutator is skew-adjoint and off-diagonal; its operator norm
equals the largest singular value of the following \(2\times2\)
cross-block B.

### Zero flux

For \(D_+\),

\[
B_+(b,c)=
\begin{pmatrix}
 b&c\\ b-1&c-1
\end{pmatrix}.
\]

The left unit row vector \((1,-1)/\sqrt2\) yields

\[
\frac{1}{\sqrt2}(1,-1)B_+
=\frac1{\sqrt2}(1,1),
\]

hence \(\|B_+\|_{\mathrm{op}}\ge1\).
Equality is attained by \(b=c=1/2\), giving a rank-one matrix
with norm 1. Therefore

\[
\boxed{d_{D_+}(00,11)=1.}
\]

### π flux

For \(D_\pi\),

\[
B_\pi(b,c)=
\begin{pmatrix}
 b&c\\ b-1&1-c
\end{pmatrix}.
\]

Its Frobenius norm satisfies

\[
\|B_\pi\|_F^2
=b^2+c^2+(b-1)^2+(1-c)^2
=1+2(b-\tfrac12)^2+2(c-\tfrac12)^2\ge1.
\]

For a \(2\times2\) matrix,
\(\|B\|_{\mathrm{op}}\ge\|B\|_F/\sqrt2\).
Thus \(\|B_\pi\|_{\mathrm{op}}\ge1/\sqrt2\).
At \(b=c=1/2\) the two columns are orthogonal, with norm
\(1/\sqrt2\), attaining equality. Hence

\[
\boxed{d_{D_\pi}(00,11)=\sqrt2.}
\]

In both models each adjacent pair has Connes distance 1.
For a neighboring pair, the corresponding matrix entry forces
the commutator norm to be at least the target difference; suitable
two-valued assignments attain equality.

The desired Hamming distance between opposite corners is 2,
so either four-dimensional adjacency choice retains a deficit.
The full independent-edge representation of LTR-MAN-09 has
Hilbert dimension 8 and exactly recovers Hamming distance.

## 3. Reproducible CPU gym

Run from repository root:

```bash
python research/logos_topos/hypercube_plaquette_gym.py
```

Requires NumPy and SciPy. It minimizes \(\|[D,f]\|\) over the two
free real vertex values with endpoint difference fixed to one,
using multiple deterministic starting points. The reciprocal minimum
is the pairwise Connes distance.

Expected opposite-vertex outputs:

| Flux | \(d(00,11)\) | \(d(01,10)\) | Hamming target |
|---|---:|---:|---:|
| 0 | 1.000000 | 1.000000 | 2 |
| \(\pi/2\) | 1.082392 | 1.082392 | 2 |
| \(\pi\) | 1.414214 | 1.414214 | 2 |

The endpoints \(0\) and \(\pi\) have the analytic minimax
certificates above. The intermediate value is a numerical
optimization result.

## 4. Mathematical consequences

The algebra of truth functions and the underlying adjacency graph
remain fixed across both matrices. A gauge-invariant phase around
the graph cycle changes the induced metric.

This suggests two independent design variables for a spectral
realization of logical structure:

- which logical truth profiles are represented;
- which off-diagonal couplings, including phases, make those
  profiles geometrically distinguishable.

For the generalized metric-capacity function \(r_{\rm geom}(m)\),
this example shows that preserving graph adjacency within a
minimal-dimensional faithful representation does not automatically
produce the desired shortest-path metric.

The exact value of \(r_{\rm geom}(2)\) within **all** finite complex
spectral triples remains open under the present analysis.
Dimension four suffices for the truth algebra and dimension eight
suffices for exact Hamming metric via independent edge blocks;
the possibility of a different Dirac realization on four through
seven complex dimensions remains a mathematical search problem.


## 5. Exact flux-phase law for the four-dimensional square

The endpoint calculations extend to **every plaquette flux**. Let each
square-edge coupling have modulus one and let the product of their
oriented phases be \(e^{i\theta}\). Gauge transformations put all
phases on the edge \(10\leftrightarrow11\).

**Theorem (written analytic proof).** The four adjacent Connes
distances are all exactly 1. Both opposite-corner distances are

\[
\boxed{d_\theta(00,11)=d_\theta(01,10)
=\sqrt{\frac{2}{1+|\cos(\theta/2)|}}.}
\]

Thus the opposite distance lies in \([1,\sqrt2]\) throughout
the phase family, while the target Hamming distance is 2.

**Proof for an opposite pair.** In the bipartite basis, fix
\(f(00)=0\), \(f(11)=1\), and write \(f(01)=b\), \(f(10)=c\).
The skew-adjoint commutator has the same operator norm as

\[
B_\theta(b,c)=
\begin{pmatrix}
b&c\\
b-1&e^{i\theta}(c-1)
\end{pmatrix}.
\]

Let \(S\) exchange the two rows and let
\(R=\operatorname{diag}(1,e^{i\theta})\).
For real \(b,c\),

\[
B_\theta(1-b,1-c)=-S\overline{B_\theta(b,c)}R.
\]

Because complex conjugation and both unitary factors preserve
operator norm, the norm is invariant under
\((b,c)\mapsto(1-b,1-c)\).
The operator norm is convex in \((b,c)\), so midpoint averaging
proves that \(b=c=1/2\) is a global minimizer.

At that midpoint,

\[
B_\theta=\frac12
\begin{pmatrix}1&1\\-1&-e^{i\theta}\end{pmatrix}.
\]

The two eigenvalues of \(B_\theta B_\theta^*\) are

\[
\lambda_\pm=\frac{1\pm|\cos(\theta/2)|}{2}.
\]

Consequently the minimum commutator norm for unit opposite
difference equals
\(\sqrt{(1+|\cos(\theta/2)|)/2}\).
By homogeneous scaling, its reciprocal is the opposite-corner
Connes distance.

For an adjacent pair, its unit-weight Dirac matrix entry gives
\(\|[D,f]\|\ge|f(u)-f(v)|\).
The Boolean-coordinate indicator separating the two endpoints
changes only across the two disjoint edges in that direction;
its commutator is a pair of scalar-size-one blocks and therefore
has norm exactly one. This proves adjacent distance one.
Square symmetry and graph gauge equivalence give the same
opposite-corner formula for the other diagonal.

The reduction to real-valued functions is valid for arbitrary complex
observables: rotate their endpoint difference to a positive real
number, then take the real part. Because \(D\) is Hermitian,
this operation weakens the commutator norm while preserving the
endpoint difference.

The formula includes the previously measured values at
\(\theta=0,\pi/2,\pi\) and upgrades the numerical phase scan
to an exact analytic one-parameter result.

The argument is currently a written proof. Its Lean formalization
requires operator-matrix norm lemmas for the complex two-by-two
plaquette and the midpoint involution.
