# LTR v0.23: Sentence-labelled Hilbert projections and Dirac commutators

**Date:** November 3, 2026

## Verified status

The Lean kernel build, explicit axiom audit, and finite regression suite passed:

- [v0.23 logical operator audit, run 41665335747](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41665335747)
- [v0.22 Lipschitz truth-projection audit, run 41664566245](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41664566245)
- [v0.21 logical Stone spectral-triple audit, run 41662893418](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41662893418)

The new modules are
[`LogicalLipschitzProjections.lean`](../../Neoplatonic/LTR/LogicalLipschitzProjections.lean)
and [`LogicalDiracObservables.lean`](../../Neoplatonic/LTR/LogicalDiracObservables.lean).

## Mathematical data

Let \(T\) be a satisfiable first-order theory, with a countable expanded
sentence type and a sentence \(\eta\) independent of \(T\).
The verified v0.21 construction chooses a compatible metric \(d\) on
Mathlib's actual Stone completion space

\[
X=T.\operatorname{CompleteType}(\alpha)
\]

and constructs a compact-resolvent complex spectral triple

\[
\bigl(\operatorname{Lip}(X,\mathbb C),
\ \ell^2(\mathbb N,\mathbb C^2),\ D\bigr).
\]

The representation \(\pi:C(X,\mathbb C)\to\mathcal B(H)\) is faithful.
Its unbounded Dirac operator \(D\) is self-adjoint, with maximal dense
domain. The ordinary resolvent \((D-iI)^{-1}\) is compact.

For each sentence \(\varphi\), define the named continuous truth
projection

\[
p_\varphi(x)=
\begin{cases}
1 &\varphi\in x,\\
0 &\varphi\notin x.
\end{cases}
\]

Its support is a clopen set. Every clopen in a compact metric space
has positive separation from its complement. Consequently the
indicator \(p_\varphi\) has some finite Lipschitz constant, even when
the chosen metric is not effectively computable.

## New verified operator statements

For every sentence \(\varphi\), let \(P_\varphi=\pi(p_\varphi)\).
The Lean proof now verifies:

1. **Admissibility.** \(p_\varphi\) belongs to the dense complex
   Lipschitz star subalgebra of the chosen Stone metric.
2. **Orthogonal projection laws.**
   \[
   P_\varphi^2=P_\varphi,\qquad P_\varphi^*=P_\varphi.
   \]
3. **Bounded infinite-dimensional commutator.** There is a bounded
   complex Hilbert operator \(C_\varphi\) and a finite real bound
   \(B_\varphi\ge0\) with \(\|C_\varphi\|\le B_\varphi\), such that
   \(\pi(p_\varphi)\) preserves \(\operatorname{Dom}(D)\) and
   \[
   D\pi(p_\varphi)\psi-\pi(p_\varphi)D\psi
   =C_\varphi\psi
   \quad(\psi\in\operatorname{Dom}(D)).
   \]
4. **Exact entailment criterion.**
   \[
   \boxed{T\models\varphi\quad\Longleftrightarrow\quad
   \|\pi(p_{\neg\varphi})\|=0.}
   \]
   Faithfulness of \(\pi\) transports the previously verified
   complex-function norm-zero criterion to an operator on \(H\).

The statements are formalized as
`complexLogicalProjection_mem_Lipschitz`,
`logicalSentence_inSpectralObservables`,
`logicalSentence_HilbertProjection`,
`logicalSentence_HilbertRefutationNorm_zero_iff`, and
`logicalSentence_boundedDiracCommutator`.

## What this means, and what remains

The named logical sentence projections are now inside the same
infinite-dimensional representation on which the self-adjoint Dirac
operator acts. The bounded commutator is proved on its maximal
domain. The norm-zero entailment test uses a genuine represented
Hilbert operator.

These are exact mathematical equivalences. A decision algorithm for
the norm is not claimed: effective uniform approximation of the
refutation norms could decide logical entailment, and the underlying
computability obstruction remains.

The chosen metric and dense completion enumeration are classical
objects. Future effective geometry must construct a controlled
metric and edge marking from sentence codes, or prove a limitation
for the chosen effective presentation. Interpretation-compatible
Dirac morphisms and a trace-class theorem are also open.

The earlier scalar spectral-energy result proves
\(\sum_j 2(1+4^j+s_j^2)^{-p/2}<\infty\) for every \(p>0\).
A global Hilbert operator trace identity is needed to package
Schatten \(p\)-summability and spectral-dimension claims.

## Reproduce

```shell
lake build Neoplatonic.LTR.Check
lake env lean Neoplatonic/LTR/Check.lean
python3 -m unittest discover -s research/logos_topos -p 'test_*.py' -v
```
