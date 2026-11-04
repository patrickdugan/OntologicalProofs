# LTR v0.34: Finite-prefix moduli and composition of numbered logical maps

**Date:** November 4, 2026

## Verification

These Lean modules passed the project's kernel build, explicit axiom report,
and finite reconstruction tests:

- [v0.32 reindexing audit, run 41757788936](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41757788936)
- [v0.33 semantic-map modulus audit, run 41758312035](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41758312035)
- [v0.34 interpretation-composition audit, run 41758731348](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41758731348)

The proof modules are
[`NumberedSentenceReindexing.lean`](../../Neoplatonic/LTR/NumberedSentenceReindexing.lean),
[`NumberedSemanticMapModulus.lean`](../../Neoplatonic/LTR/NumberedSemanticMapModulus.lean),
and
[`NumberedSemanticMapComposition.lean`](../../Neoplatonic/LTR/NumberedSemanticMapComposition.lean).

The metric and numbered spectral-triple foundations are described in the
[prior v0.31 ledger](INFINITE_DIRAC_V31.md).

## Enumeration dependence of the metric

For a first-order theory `T`, let `X` be Mathlib's complete-type
Stone space. For any surjective numbering of its expanded-language
sentences `c : ℕ → Sentence`, the verified numbered metric satisfies

[
d_c(p,q)=
egin{cases}
0 & p=q,\\
2^{-N_c(p,q)} & p\ne q,
end{cases}
]

where `N_c(p,q)` is their first differing numbered sentence index.

The v0.31 finite-prefix theorem states

[
d_c(p,q)\le2^{-n}
\iff
\forall i<n,\bigl(c(i)\in p\iff c(i)\in q\bigr).
]

## The explicit index-prefix modulus

Suppose the source numbering is `c` and the target numbering is
`c'`. A lookup `k : ℕ → ℕ` satisfies

[
c(k(j))=c'(j).
]

Define the finite index modulus

[
\boxed{M_k(n)=\max\bigl(\{k(j)+1:j<n\}\cup\{0\}\bigr).}
]

The Lean proof `sentenceIndexPrefixModulus_gt` verifies
`k(j)<M_k(n)` for `j<n`. Consequently, if completions `p,q`
agree on every source sentence in the first `M_k(n)` positions,
they agree on every target sentence in the first `n` positions.

The `numberedSentenceMetric_radiusTransfer_of_lookup` theorem
translates that statement into an exact metric implication:

[
\boxed{
d_c(p,q)\le2^{-M_k(n)}
\ \Longrightarrow\ 
d_{c'}(p,q)\le2^{-n}.
}
]

Under surjectivity of `c`, the lookup exists by classical choice.
The theorem `numberedSentenceMetric_radiusTransfer` packages this
existence into a finite-prefix modulus. In either direction, one
can bound the target distance below an arbitrary positive tolerance;
`numberedSentenceMetric_uniformModulus` proves the corresponding
epsilon-delta estimate. This formally gives uniform equivalence
between the numbered ultrametrics on the same completion space.

A computable lookup makes `M_k` a finite calculation. The Lean
proof makes no claim that arbitrary classical lookup choices are
computable, or that sentence truth in a completion is decidable.

## Maps between different logical Stone spaces

Let `F : X₁ → X₂` be a function on genuine complete-type spaces
of potentially different first-order theories. Write `c₁,c₂` for
surjective sentence numberings and suppose the following semantic
pullback identity holds for an index map `k`:

[
\boxed{
c_2(j)\in F(p)
\iff c_1(k(j))\in p.
}
]

The `numberedSemanticMap_prefixTransfer` theorem shows that
agreement of two source completions on the first `M_k(n)` source
sentences forces agreement of their images on the first `n`
target sentences.

Thus `numberedSemanticMap_radiusTransfer` proves

[
d_{c_1}(p,q)\le2^{-M_k(n)}
\implies
d_{c_2}(F(p),F(q))\le2^{-n}.
]

For every `ε>0`, the theorem
`numberedSemanticMap_uniformModulus` constructs a positive
`δ` for which the source distance below `δ` forces
the image distance below `ε`. The statement works across
distinct sentence types and theories.

The semantic-pullback hypothesis is explicit. The theorem does
not assert that every syntactic language map automatically
provides such an `F` and `k`.

## Composition laws

Suppose `F : X₁ → X₂` and `G : X₂ → X₃` satisfy their
sentence-truth laws with lookups `k` and `l` respectively.
Lean verifies that the composite `G ∘ F` satisfies the law with
lookup `k ∘ l`.

Its exact lookup modulus is bounded by nested moduli:

[
\boxed{
M_{k\circ l}(n)\le M_k(M_l(n)).
}
]

The theorem `numberedSemanticMap_comp_prefixTransfer` verifies
the corresponding implication between finite sentence prefixes.
The theorem `numberedSemanticMap_comp_radiusTransfer` verifies
the composition bound in the source and target ultrametrics:

[
\boxed{
d_{c_1}(p,q)\le2^{-M_k(M_l(n))}
\implies
d_{c_3}\bigl(G(F(p)),G(F(q))\bigr)\le2^{-n}.
}
]

This is a compositional quantitative rule for semantic maps
that preserve the indexed sentence truth values.

## Remaining scope

The results are mathematically conditional on named sentence
enumerations, surjectivity, and stated semantic truth-pullback
identities. A dedicated effective syntax presentation and a
fully instantiated network of theory interpretations remain to
be formalized before claims of algorithmic computation can follow.

Continuity of the completion-space maps and faithful pullback
of logical projections do not automatically yield a unitary
intertwiner of the unbounded Dirac operators. The earlier
scalar spectral-energy summability theorem also remains
distinct from a global Schatten-class operator trace theorem.

## Reproduction

```shell
lake build Neoplatonic.LTR.Check
lake env lean Neoplatonic/LTR/Check.lean
python3 -m unittest discover -s research/logos_topos -p 'test_*.py' -v
```
