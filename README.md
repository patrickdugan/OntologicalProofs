# The One from the Many? Lean 4, version 2

A falsification-oriented formalization of several Neoplatonic and
Avicennian arguments concerning a unique ground of reality.

## Scope and verification status

The target of the theorems is **one ungrounded source of every object
in a model of ontological priority**. Such an object is not automatically
an omniscient, perfectly good, conscious, or personal deity. Nothing in
these results proves that physical reality satisfies the grounding axioms.

The Lean 4 modules are written without `sorry` or theorem-level `axiom`
declarations. **Compilation status (2026-10-17):** all modules compile against current mathlib (Lean v4.35.0) with no `sorry`; the main theorems depend only on `propext`, `Classical.choice`, `Quot.sound`. See `COMPILE_NOTES.md` for the fixes made. The metaphysical premises (common effects, local coherence, single parent, and the RH bridge `spectralAlignmentToCommonPrior`) remain assumptions, not theorems.

## Theorems and epistemic status

| Module | Statement | Source of substantive assumptions |
|---|---|---|
| `Core.lean` | Well-foundedness + common ancestors imply a unique universal root | **Common ancestry is assumed** |
| `Amalgamation.lean` | Well-foundedness + common *effects* + unique direct parent imply a unique universal root | The unique-parent constraint is very strong |
| `LocalConfluence.lean` | Well-foundedness + common effects + **local ancestral coherence of co-grounds** imply a unique universal root | Local coherence and common effects are metaphysical axioms |
| `Symmetry.lean` | A uniquely distinguished point must be fixed by every predicate-preserving symmetry; integer translation forbids a unique invariant integer | Pure mathematics |
| `RHGeometry.lean` | RH + a nontrivial zeta zero imply a unique shared real coordinate 1/2 among nontrivial zeros | RH remains an open conjecture; zero existence is an explicit premise |
| `RH.lean` | The actual mathlib RH implies critical-zero alignment; optional speculative bridge derives first principle | Spectral-to-ontology bridge **unjustified** |
| `Models.lean`, `MergeModel.lean` | Explicit failures when unity conditions are absent | Pure mathematical countermodels |
| `CoherentModel.lean` | A concrete grounding system with two immediate co-grounds satisfies the local-confluence version | Pure mathematical consistency witness |
| `Modal.lean` | Modal necessity does not imply being ungrounded | Pure mathematical countermodel |

## Main result of version 2: backward confluence

Interpret `prior x y` as `x` being an **immediate** explanatory ground of `y`.
Let `Reach prior x y` be the reflexive-transitive closure, so the same
notation also covers multi-step grounding histories.

Define:

1. `wf`: the relation is well-founded, ruling out endless regress along
   immediate grounding edges.
2. `commonEffect`: for all x,y, there is z such that `Reach prior x z`
   and `Reach prior y z`. Everyone can contribute to one composite.
3. `localCoherence`: if `prior x z` and `prior y z`, there exists w with
   `Reach prior w x` and `Reach prior w y`. Every pair of immediate co-grounds
   has ancestrally compatible explanatory histories.
4. A seed element exists.

Then:

```
existsUnique g, Root prior g AND forall x, Reach prior g x
```

Proof strategy: well-founded induction guarantees each object has a
root ancestor. By a Newman-style induction on the common descendant,
local coherence makes its root ancestor unique. The common-effect
condition forces the roots of any pair of objects to agree. Thus every
object descends from one root. The proof carries no `God` predicate and
makes no mathematical assertions about supernatural attributes.

This condition **allows causal branching and merging**. For instance,
`CoherentModel.lean` has three objects and these edges:

```
       origin
       /   \\
      v     v
   branch -> apex
```

The apex has two distinct immediate grounds, both tracing to `origin`.
This refutes the idea that the revised theorem secretly requires a
linear or single-parent causal chain.

## Objection and research agenda

- The `commonEffect` assumption amounts to a global connectedness or
  compositionality principle. Theorems based on local coherence alone
  permit multiple independent worlds / foundations.
- The `localCoherence` assumption rules out two *fundamentally independent*
  explanatory histories meeting at a composite. This is the main
  philosophical point to interrogate, not a consequence of number theory.
- In categorical language, the abstract first principle resembles an
  initial object in a thin category of grounding reachability. Uniqueness
  is characteristic of initial objects, while the **existence** of such
  an object always requires structural hypotheses beyond bare category
  axioms.
- Avicenna's `necessary-through-itself` is richer than `Root prior`.
  A modal/grounding bridge would need to be specified separately.
- Prove the underlying confluence theorem in mathlib's `Relation` API
  and link it to normal-form uniqueness; then seek weaker natural axioms
  on physical, conceptual, or computational compositionality.

## RH branch

Mathlib defines the genuine `RiemannHypothesis` in
[`Mathlib.NumberTheory.LSeries.RiemannZeta`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/NumberTheory/LSeries/RiemannZeta.html).

Under RH, the common real coordinate of the nontrivial zero spectrum
is 1/2. `RHGeometry.lean` adds a witness of a nontrivial zero so the
common coordinate is **uniquely** characterized. This is an authentic
conditional mathematical statement about the zeta function.

In `RH.lean`, a separate field `spectralAlignmentToCommonPrior` is
**exactly the unsupported bridge** from number theory to metaphysics.
The RH extension cannot serve as a God proof without independent
argument for that bridge. `RHGeometry.lean` deliberately avoids that
problem by stating only the spectral consequence.

## Exhaustive finite audits

Run:

```
python audit_models.py
python audit_v2.py
python audit_confluence.py
```

For all labeled loopless DAGs with 1 to 4 nodes, the audit checks
`commonEffect`, `localCoherence`, and the unique-universal-root
conclusion. Of the 543 four-node DAGs, 216 satisfy both substantive
structural conditions, **0 violate the conclusion**, and **192 permit
more than one immediate parent**. This is a finite-model falsification
check, not a Lean kernel proof.

## Compile with Lean/mathlib

From inside a compatible mathlib-enabled Lean 4 project, copy `Neoplatonic/`
into the root and run:

```
lake env lean Neoplatonic/Core.lean
lake env lean Neoplatonic/Amalgamation.lean
lake env lean Neoplatonic/LocalConfluence.lean
lake env lean Neoplatonic/Symmetry.lean
lake env lean Neoplatonic/Models.lean
lake env lean Neoplatonic/MergeModel.lean
lake env lean Neoplatonic/CoherentModel.lean
lake env lean Neoplatonic/Modal.lean
lake env lean Neoplatonic/RH.lean
lake env lean Neoplatonic/RHGeometry.lean
```

A good next acceptance gate is to run all commands under a pinned mathlib
commit in CI, compare results to the finite audits, and inspect
`#print axioms` for the main theorems. At present, the limitations above
prevent asserting that Lean accepted the scripts.
