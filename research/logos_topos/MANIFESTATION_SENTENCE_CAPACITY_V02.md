# LTR-MAN-02: Named diagonal sentences, finite-fragment capacity, and nonuniform recovery

**November 4, 2026.** Connected to the actual one-axiom nullary first-order theory and its genuine complete-type Stone space.

## Concrete sentence instead of an anonymous clopen

For a finite list of completions \(s_i\), the construction selects the opposite literal at coordinate \(i\):

\[
\ell_i(s)=
\begin{cases}
\neg P_i,&P_i\in s_i,\\
P_i,&P_i\notin s_i.
\end{cases}
\qquad
\Phi_s=\bigwedge_{i<n}\ell_i(s).
\]

This is a *first-order sentence* in the expanded nullary language, built using Mathlib's syntax-level meet and top. The module `Neoplatonic/LTR/ManifestationSentence.lean` constructs it as a finite fold of actual sentence objects. Its semantic truth locus is exactly the diagonal cylinder:

\[
T.\mathrm{typesWith}(\Phi_s)
=
\{p:\forall i<n,\operatorname{decode}(p)(i)
=\neg\operatorname{decode}(s_i)(i)\}.
\]

The diagonal completion \(\operatorname{encode}(b_s)\) satisfies \(\Phi_s\), and every member of the sample refutes it. The empty sample gives the tautology.

### Named operator gap

The previous `effectiveNullaryStoneSpectralTriple` assigns a faithful Hilbert representation to the complex characteristic function of \(\Phi_s\). By the named sentence projection theorem, the resulting operator \(P_{\Phi_s}\) is self-adjoint and idempotent. The constructed satisfying completion implies the continuous truth projection has norm one. Faithfulness and the C*-identity then give

\[
\boxed{\|P_{\Phi_s}\|=1.}
\]

Every member of \(s\) evaluates its underlying continuous truth function to zero. Thus this result directly connects a concrete finite-sample diagonal to the actual infinite-dimensional Hilbert realization.

**Status:** The Lean module and its axiom prints are wired into `Neoplatonic/LTR/Check.lean`. Refer to the latest green CI record for kernel-verification status.

## Exact finite-fragment capacity

For the first \(m\) nullary predicates, define the restriction to an \(m\)-bit prefix:

\[
r_m:X\to 2^m,\qquad
r_m(p)(i)=\operatorname{decode}(p)(i).
\]

All \(2^m\) assignments occur in the concrete model. The algebra of continuous observables depending only on these \(m\) coordinates is

\[
A_m\cong\mathbb C^{2^m}.
\]

It has \(2^m\) pairwise orthogonal nonzero minimal truth projections and \(2^{2^m}\) Boolean elements. A family of \(n\) point evaluations is faithful on \(A_m\) if and only if its \(m\)-coordinate projection is surjective onto \(2^m\). Hence

\[
\boxed{N_{\mathrm{min}}(m)=2^m.}
\]

The Lean module `ManifestationCapacity.lean` constructs a canonical finite family of complete theories of size \(2^m\), verifies that their restrictions cover every prefix, proves the converse bound \(2^m\le n\) for any covering family, and produces a missing truth assignment whenever \(n<2^m\).

In dimension language, a faithful unital star representation \(A_m\to M_d(\mathbb C)\) requires \(d\ge2^m\), as images of pairwise orthogonal nonzero minimal projections consume distinct nonzero subspaces. This matrix rank argument is a standard written corollary; its standalone Lean formalization remains a next step.

## Pointwise exactness alongside maximum finite-depth error

Let \(q:\mathbb N\to X\) have dense range in the Stone topology. For a genuine sentence \(\varphi\), define

\[
E_N(\varphi)=
\begin{cases}
1,&\exists j<N:\varphi\in q(j),\\
0,&\text{otherwise}.
\end{cases}
\]

Every named truth locus is clopen, so density finds a sample point inside every nonempty truth locus. For each fixed sentence \(\varphi\), a finite cutoff \(N_\varphi\) therefore exists, after which

\[
E_N(\varphi)=
\|\mathbf1_{U_\varphi}\|_\infty,
\quad N\ge N_\varphi.
\]

For each finite \(N\), diagonalize against the first \(N\) samples. Then

\[
E_N(\Phi_N)=0,\quad
\|\mathbf1_{U_{\Phi_N}}\|_\infty=1.
\]

Since all truth projection norms lie in \([0,1]\), the exact worst-case discrepancy over all named sentences is

\[
\boxed{\sup_{\varphi}|E_N(\varphi)-
\|\mathbf1_{U_\varphi}\|_\infty|=1
\quad\text{for every finite }N.}
\]

`ManifestationFiniteRecovery.lean` formalizes this as a real-valued 0/1 finite detection norm, an eventual-exactness theorem, a universal error bound, and a diagonal witness attaining the bound for each finite cutoff. The final statement is proved with a universal bound plus a named witness, avoiding any artificial global computable supremum over all first-order sentences.

**A useful inference:** faithful infinite reconstruction can coexist with the absence of any uniform finite depth that recovers every named logical distinction. This is a formal instance of pointwise convergence without uniform convergence over a noncompact family of observables.

## Where to extend the theory

The most important next experiment is to tie the prefix capacity \(2^m\) to the actual ordered dense-pair marking of the Hilbert spectral triple, rather than an arbitrary sample. For the chosen sequence \(q\), define

\[
K(m):=1+\max_{b\in 2^m}
\min\{j:r_m(q_j)=b\}.
\]

Density ensures that \(K(m)<\infty\), and cardinality forces \(K(m)\ge2^m\). The present dense marking is selected classically and its index bounds are not computationally certified. A constructive prefix-cover algorithm and an effective or probabilistic bound on \(K(m)\) would connect this result to truncation complexity.

The mathematical word *manifestation* here denotes the representation of syntactic truth conditions as clopen loci and operators. Its Sufi/Shia *tajallī* interpretation is a philosophical analogy and does not enter any Lean axioms.

## Reproduce

```sh
lake build Neoplatonic.LTR.Check
lake env lean Neoplatonic/LTR/Check.lean
python3 -m unittest discover -s research/logos_topos -p 'test_*.py' -v
```
