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
| `RH.lean` | The actual mathlib RH implies critical-zero alignment; optional speculative bridge derives first principle | Bridge field shown **vacuous** (interdefinable with `commonPrior` under RH); retained as documentation |
| `Models.lean`, `MergeModel.lean` | Explicit failures when unity conditions are absent | Pure mathematical countermodels |
| `CoherentModel.lean` | A concrete grounding system with two immediate co-grounds satisfies the local-confluence version | Pure mathematical consistency witness |
| `Modal.lean` | Modal necessity does not imply being ungrounded | Pure mathematical countermodel |
| `Arithmetic.lean` | Proper divisibility on ℕ⁺ is a confluent ground theory with unique first principle 1; with the unit removed the roots are exactly the primes, local coherence fails at 6, and common ground ⇔ non-coprime; `riemannZeta` is the L-series of this order's incidence zeta | Pure mathematics |

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

## Arithmetic as a model: what the One costs

`Arithmetic.lean` supplies the natural infinite model of the version-2 axioms.
Take `prior d n` to mean `d` is a proper divisor of `n` on the positive
naturals. This is well-founded, branches (2 and 3 are incomparable immediate
grounds of 6) and merges, satisfies `commonEffect` (products) and
`localCoherence` (the unit is below everything), and has the unique first
principle `1`: the empty product, the ground of everything by contributing
no determination.

Remove the unit and the picture inverts. On `{n | 2 ≤ n}` the roots are
exactly the primes (`root₂_iff_prime`), there are unboundedly many of them
(`roots₂_unbounded`), `commonEffect` still holds, `localCoherence` fails at
6 (`not_locally_coherent₂`), no first principle exists
(`no_first_principle₂`), and two beings have a common ground iff they are
not coprime (`common_ground_iff_not_coprime`).

So arithmetic's answer to "is there a One" is: iff the unit is counted. This
is the strongest statement available of what `localCoherence` costs. The
Riemann zeta function enters only here: for `Re s > 1` it is the L-series of
the incidence zeta function of this divisibility order, and `ζ * μ = 1`
isolates the unit. Its zeros do not enter.

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

`RHGeometry.lean` states a conditional mathematical fact: under RH, with one
nontrivial zero as witness, the nontrivial zeros share the unique real
coordinate 1/2. Note that symmetry of the zeros about 1/2 is unconditional
(functional equation); RH is the collapse of each symmetric pair onto the line.

`RH.lean` contains the retired bridge `spectralAlignmentToCommonPrior`. Its
antecedent `SpectralAligned` is a closed proposition about ℂ with no variable
in common with `prior`, so the field is extensionally `¬SpectralAligned ∨
commonPrior`, i.e. `commonPrior` under RH. `RHGroundTheory.ofGroundTheory`
and `RHGroundTheory.toGroundTheory` make this interdefinability explicit. The
zeta zeros do no inferential work and no reformulation of RH (Hilbert–Pólya,
Weil/Li positivity, random-matrix statistics) changes this: every relation ζ
provides between primes and zeros is a symmetric identity between two
encodings of one object, while grounding is asymmetric and well-founded.

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
lake env lean Neoplatonic/Arithmetic.lean
```

A good next acceptance gate is to run all commands under a pinned mathlib
commit in CI, compare results to the finite audits, and inspect
`#print axioms` for the main theorems. At present, the limitations above
prevent asserting that Lean accepted the scripts.
