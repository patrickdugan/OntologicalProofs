# LTR v0.42: Constructive sentence codes and a concrete logical spectral triple

**November 4, 2026.**

## Verified proof modules

| Version | Module | Successful workflow |
|---|---|---|
| v0.39 | [NullaryEffectiveSyntax.lean](../../Neoplatonic/LTR/NullaryEffectiveSyntax.lean) | [41763354222](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41763354222) |
| v0.40 | [NullaryEffectiveMetricModulus.lean](../../Neoplatonic/LTR/NullaryEffectiveMetricModulus.lean) | [41763726787](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41763726787) |
| v0.41 | [NullaryEffectiveSpectralTriple.lean](../../Neoplatonic/LTR/NullaryEffectiveSpectralTriple.lean) | [41764177037](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41764177037), combined-head audit |
| v0.42 | [NullaryEffectiveHilbertOperators.lean](../../Neoplatonic/LTR/NullaryEffectiveHilbertOperators.lean) | [41764603196](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41764603196) |

These runs checked the Lean proof build, printed theorem axiom dependencies, and passed the repository's finite tests. The initial run for v0.41 was cancelled by another concurrent commit; its successor passed on a head containing both developments.

## A constructive code for full first-order syntax

The concrete language has relation symbols indexed by naturals at arity zero and no others; function-symbol sorts are empty. Mathlib's `ModelTheory/Encoding.lean` defines total list encoders and decoders for first-order terms and bounded formulas, with proved round trips.

We install `Encodable` instances for the actual nullary signature, its dependent indexed terms, its bounded formulas, its original-language sentences, and the empty-constant expanded sentence type. The last transport uses Mathlib's `LEquiv.addEmptyConstants` equivalence. These encodings cover arbitrary quantified sentences.

The new functions

\[
\operatorname{encode}:\operatorname{Sentence}(L[[\mathrm{Empty}]])\to\mathbb N,
\qquad
\operatorname{decode}:\mathbb N\to\operatorname{Option}(\operatorname{Sentence}(L[[\mathrm{Empty}]]))
\]

satisfy the verified exact equation

\[
\boxed{\operatorname{decode}(\operatorname{encode}(\varphi))=\operatorname{some}(\varphi).}
\]

A total sentence enumeration uses the partial decoder, returning the syntactically valid fallback \(\bot\) for unused codes. It is surjective, with witness \(\operatorname{encode}(\varphi)\).

For a real partial-recursive program \(e\), its verified full first-order sentence transformation is \(\sigma_e\). The **direct index lookup** is

\[
\boxed{k_e(j)=\operatorname{encode}(\sigma_e(\operatorname{code}(j))).}
\]

Lean proves \(\operatorname{code}(k_e(j))=\sigma_e(\operatorname{code}(j))\) and the corresponding truth pullback for every genuine complete type.

The index prefix modulus

\[
M_e(n)=\max\left(\{k_e(j)+1:j<n\}\cup\{0\}\right)
\]

is a total finite computation over this lookup. Lean proves the metric implication

\[
\boxed{d(p,q)\le 2^{-M_e(n)}
\Longrightarrow d(F_e(p),F_e(q))\le 2^{-n}.}
\]

For two codes \(e,f\), it also proves the nested modulus

\[
d(p,q)\le 2^{-M_e(M_f(n))}
\Longrightarrow d(F_f(F_e(p)),F_f(F_e(q)))\le2^{-n}.
\]

## A fully instantiated nullary Stone spectral triple

The theory's satisfiability is certified by an actual singleton model, and the zeroth nullary predicate is independent by explicit all-true and all-false models. Those theorems eliminate the two former theory-specific hypotheses in the concrete construction.

Using the constructive sentence numbering and the proved general spectral-triple constructor, `effectiveNullaryStoneSpectralTriple` supplies a compact complex spectral triple over the actual space \(X=T.\mathrm{CompleteType}(\mathrm{Empty})\).

Its faithful complex representation acts on \(H=\ell^2(\mathbb N,\mathbb C^2)\). The unbounded Dirac is maximal-domain self-adjoint, its ordinary resolvent compact, and its admissible complex Lipschitz algebra dense. The existing all-dense-pairs theorem recovers the first-disagreement metric from the bounded commutator norm.

For each expanded sentence \(\varphi\), the represented operator \(P_\varphi=\pi(p_\varphi)\) is an orthogonal projection:

\[
P_\varphi^2=P_\varphi,\qquad P_\varphi^*=P_\varphi.
\]

Every such named operator preserves the Dirac domain and has a bounded commutator. Lean proves the exact semantic norm criterion

\[
\boxed{T\models\varphi\iff\|\pi(p_{\neg\varphi})\|=0.}
\]

## Boundaries of the result

The term, formula and sentence encoders and the finite index lookup are constructive Lean definitions. The project has verified their round-trip, index, semantic and metric theorems. Mathlib itself lists formal `Primcodable` and primitive-recursion instances for general first-order syntax as outstanding tasks, so this development **does not yet prove a Mathlib `Primrec` or `Computable` predicate** for the substitution function.

There is currently no measured runtime or natural-code bit-size bound. Pairing-based encodings can produce large integers, so executable source alone does not establish a practical high-throughput implementation.

The spectral triple still uses a classically selected dense sequence of completed theories. The code does not construct a truth oracle for arbitrary completions, compute the global Dirac operator, or prove a Dirac intertwiner for general logical interpretations. Operator Schatten-class summability remains a separate global trace-class obligation.

The concrete one-axiom nullary theory is not being used as an arithmetic theory with undecidable entailment. The earlier generic undecidability-transfer theorem has an explicit premise concerning the underlying theory; it is not silently invoked here.

## Reproduce

```shell
lake build Neoplatonic.LTR.Check
lake env lean Neoplatonic/LTR/Check.lean
python3 -m unittest discover -s research/logos_topos -p 'test_*.py' -v
```
