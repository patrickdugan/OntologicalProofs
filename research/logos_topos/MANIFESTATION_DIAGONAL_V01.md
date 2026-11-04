# LTR-MAN-01: Finite manifestation, diagonal truth, and the norm-one loss

**November 4, 2026.** Scope: a theorem about the actual Stone space of complete first-order theories of the one-axiom nullary theory, alongside an analytic corollary proved here on paper.

## 1. The mathematical objects

The repository already proves that the complete-type space

\[
X=T.\mathrm{CompleteType}(\mathrm{Empty})
\]

is homeomorphic to the Cantor space \(2^{\mathbb N}\) through
\(\operatorname{decode}:X\to 2^{\mathbb N}\) and
\(\operatorname{encode}:2^{\mathbb N}\to X\).
See `NullaryTopology.lean` and `NullaryCompleteness.lean`.
Each Boolean coordinate is the truth value of a genuine lifted
nullary first-order sentence. A finite conjunction of coordinate
conditions therefore determines a clopen truth locus.

The infinite Hilbert-space representation in
`NullaryEffectiveHilbertOperators.lean` is faithful and assigns
self-adjoint truth projections to actual first-order sentences.

## 2. Diagonal manifestation theorem

**Theorem (kernel-checked module target).** For every natural number
\(n\) and every indexed finite sample
\[
s:\{0,\ldots,n-1\}\to X
\]
there exists a nonempty clopen \(U_s\subseteq X\) satisfying
\[
\forall i<n,\quad s_i\notin U_s.
\]
The witness is defined by at most \(n\) literal truth conditions
on the first \(n\) nullary predicates.

**Construction.** Define Boolean bits \(b_s\in 2^{\mathbb N}\) by
\[
b_s(k)=
\begin{cases}
1-\operatorname{decode}(s_k)(k),&k<n,\\
0,&k\ge n.
\end{cases}
\]
Let
\[
U_s=\{p\in X:\forall i<n,\ 
\operatorname{decode}(p)(i)=1-\operatorname{decode}(s_i)(i)\}.
\]
The complete type \(\operatorname{encode}(b_s)\) belongs to \(U_s\)
by the established decode/encode inverse. For each sample \(s_i\),
membership in \(U_s\) would imply a Boolean bit equals its negation.
That contradiction excludes \(s_i\). Continuity of each Boolean
coordinate and finiteness of the intersection prove that \(U_s\)
is clopen.

This proof works with duplicate samples and with \(n=0\). In the
latter case the empty conjunction describes all of \(X\), as it should.

**Formal Lean declarations:** `manifestationDiagonalBits`,
`manifestationCylinder`, `manifestationDiagonal_mem`,
`manifestationCylinder_misses`, `manifestationCylinder_isClopen`,
`finiteManifestation_obstruction`, and
`finiteManifestation_not_conservative`.

The finite-sample nonconservativity conclusion says that
\[
\neg\bigl[\forall U\subseteq X\ \text{clopen},\quad
U\ne\varnothing\iff (\exists i<n:s_i\in U)\bigr].
\]

## 3. Exact operator-norm gap (analytic corollary)

In the commutative C*-algebra \(C(X,\mathbb C)\), the indicator
\(p_s=1_{U_s}\) is a continuous self-adjoint projection. Because
\(U_s\ne\varnothing\),
\[
\boxed{\|p_s\|_\infty=1.}
\]
Consider the finite point-evaluation star homomorphism
\[
\rho_s:C(X,\mathbb C)\to\mathbb C^n,\quad
\rho_s(f)=(f(s_0),\ldots,f(s_{n-1})).
\]
The separating projection has
\[
\boxed{\rho_s(p_s)=0\quad\text{and}\quad
\|p_s\|_\infty-\|\rho_s(p_s)\|=1.}
\]
Thus finite point sampling is not faithful and cannot approximate
*all* projection norms with uniform error smaller than one half.
This argument is an immediate mathematical consequence of the
constructed clopen set. The operator-level corollary is currently a
written proof, not a new Lean theorem about \(C(X,\mathbb C)\).

### General finite-dimensional obstruction

There is a stronger standard argument. Cantor space admits arbitrarily
many pairwise disjoint nonempty clopen cylinders. Suppose that a faithful
star homomorphism
\(\pi:C(X,\mathbb C)\to M_d(\mathbb C)\) existed.
Choose \(d+1\) such cylinders \(U_i\). Their projections
\(1_{U_i}\) are nonzero and mutually orthogonal. Faithfulness and
multiplicativity would send them to \(d+1\) nonzero mutually
orthogonal projections on \(\mathbb C^d\), requiring at least
\(d+1\) orthogonal nonzero subspaces in dimension \(d\).
Contradiction.

The general finite-dimensional matrix statement is a written
proof here; the present Lean code verifies the explicit finite-sample
Stone-space obstruction.

## 4. How this interfaces with the existing infinite triple

The v0.42+ theorem
`effectiveNullary_refutationNorm_zero_iff_entails` establishes,
for the *existing* faithful Hilbert representation \(\pi\),
\[
T\models\varphi
\iff \|\pi(p_{\neg\varphi})\|=0.
\]
Its domain is an infinite-dimensional Hilbert space, and the
representation itself is classical rather than a computable global
oracle. In contrast, any fixed finite collection of completed
theories misses some clopen truth locus by the new diagonal theorem.

An explicit named first-order *sentence* for \(U_s\) can be formed
as the conjunction of the first \(n\) appropriate positive or
negative lifted atoms. The Lean development currently verifies
the corresponding clopen **semantic locus**; the syntax-level
conjunction-to-operator bridge is the next formalization task.

## 5. Topos bridge and the theological interpretation

The object verified here is a **Stone space**; it is not yet a
proof of a geometric morphism between classifying topoi.
One can form the sheaf topos \(\mathbf{Sh}(X)\) and study the
Boolean algebra of clopen subobjects. Establishing a functorial
translation between first-order syntax, the appropriate logical
topos, and the existing analytic triple requires an explicit
interpretation and naturality theorem.

In the philosophical vocabulary of *Divine Elegance*, a
*maẓhar*, a locus of manifestation, may be
modeled as a partial realization of a richer source of logical
distinctions. The mathematical result controls fidelity of a
specified representation. It makes no assertion about Jesus,
divinity, incarnation, or shirk. A proposed Christological
application must supply its own account of what the Word and
the human locus denote.

### Exact finite-fragment capacity

For the first \(m\) independent nullary predicates, the Boolean
subalgebra they generate has exactly \(2^m\) nonzero atoms, one for
each length-\(m\) truth assignment. The associated function algebra is

\[
A_m \cong \mathbb C^{2^m}.
\]

A sample restricted to \(A_m\) is faithful **if and only if** it meets
every one of those \(2^m\) cylinders. Consequently the smallest sample
that preserves the entire finite-fragment algebra has exactly

\[
\boxed{N_{\min}(m)=2^m.}
\]

Necessity follows by applying the diagonal nonempty-projection argument
to an unrepresented atom. Sufficiency follows because any element of
\(A_m\) is constant on each atom; taking one representative per atom
preserves its supremum norm. Equivalently, a faithful star representation
of \(A_m\) on a Hilbert space \(H\) requires
\(\dim H\ge 2^m\), since the minimal atomic projections must have
nonzero pairwise orthogonal images.

The explicit n-coordinate diagonal of Section 2 is constructive from
a given n-sample. The cardinality theorem improves its existence
bound: to defeat a sample of n points, a cylinder using only
\(\lceil\log_2(n+1)\rceil\) coordinate literals suffices.

For the existing countable dense sequence of marked completed theories,
a finite coverage index can be defined as

\[
K(m)=1+\max_{b\in 2^m}\min\{j:\operatorname{prefix}_m(s_j)=b\}.
\]

It is finite by density. The current chosen sequence is classical, so
this definition supplies no effective numerical bound without further
constructive data. This leads to a useful measurement target:
**finite-fragment faithfulness at bounded Hilbert truncation depth**.

### The precise topos-level interpretation

Let \(\mathcal E=\mathbf{Sh}(X)\). Clopen truth loci are
complemented subterminal objects of this sheaf topos.
The finite set of sample points defines a continuous map from a
discrete n-point space to X and hence a geometric morphism whose
inverse image is the tuple of stalks

\[
q_S^*:\mathbf{Sh}(X)\longrightarrow\mathbf{Set}^n.
\]

On the named clopen truth objects it simply records the Boolean
membership vector. For the nonempty clopen \(U_s\) built above,
\(q_S^*(U_s)=0\). The map \(0\to U_s\) thus becomes an isomorphism
under \(q_S^*\), although it was not an isomorphism in
\(\mathbf{Sh}(X)\). Therefore finite point-evaluation is
**nonconservative as a geometric inverse-image functor**.

This categorical consequence is a written argument using standard
sheaf-topos semantics, not yet formalized in Lean.

There is a further boundary: even a countable dense sample can
detect every nonempty open truth locus and every nonzero continuous
function, but generally cannot test isomorphisms of *all* sheaves.
For any omitted point y, the map from the terminal sheaf to a
two-element skyscraper sheaf at y (selecting one element) is an
isomorphism on all sampled stalks and fails at y.
Thus the C*-algebra and the full sheaf topos have different
requirements for faithful observation.

This distinction prevents identifying the existing faithful
Hilbert representation of C(X) with a reconstruction of all of
\(\mathbf{Sh}(X)\).

## 6. Next formal targets

1. Construct the actual finite conjunction `diagonalSentence`
   in `L[[Empty]].Sentence`, prove its truth locus equals
   `manifestationCylinder`, and use the named logical Hilbert
   projection from v0.42.
2. Formalize the norm-one defect for the finite evaluation
   star-homomorphism and a general finite-dimensional rank obstruction.
3. Make the categorical step precise: functorial Boolean syntax
   interpretation into \(\mathbf{Sh}(X)\), carrying named clopens
   into projections, then a naturality condition relating operator
   representations of distinct theory spaces.
4. Distinguish preservation of a selected fragment of propositions
   from total faithfulness. The size and difficulty of the fragment
   should enter a quantitative fidelity bound.

## Reproduction

```shell
lake build Neoplatonic.LTR.Check
lake env lean Neoplatonic/LTR/Check.lean
```

Check the GitHub Actions record before describing the new Lean
module as kernel-verified.
