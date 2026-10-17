# The One from the Many? Lean 4, version 2

A falsification-oriented formalization of several Neoplatonic and
Avicennian arguments concerning a unique ground of reality.

## Scope and verification status

The target of the theorems is **one ungrounded source of every object
in a model of ontological priority**. Such an object is not automatically
an omniscient, perfectly good, conscious, or personal deity. Nothing in
these results proves that physical reality satisfies the grounding axioms.

The Lean 4 modules are written without `sorry` or theorem-level `axiom`
declarations. **Compilation status (2026-10-18):** all 14 modules compile against current mathlib (Lean v4.35.0) with no `sorry`; the main theorems depend only on `propext`, `Classical.choice`, `Quot.sound`. See `COMPILE_NOTES.md` for the fixes made. The metaphysical premises (common effects, local coherence, single parent, and the RH bridge `spectralAlignmentToCommonPrior`) remain assumptions, not theorems.

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
| `GodelScott.lean` | Scott's axioms give □∃x G(x) and modal collapse in KB; collapse follows from D2 alone; Scott's axioms have a model; Gödel's 1970 axioms are inconsistent in K | **A1–A5 are assumed** (structure fields) |
| `GodelAnderson.lean` | Anderson's emendation gives □∃x G*(x) in S5; an S5 model of it has no modal collapse | **A1*–A5 are assumed** (structure fields) |
| `GodelGrounding.lean` | One model satisfies Scott's axioms and the grounding axioms with the God-like being ≠ the first principle; they coincide under A6 | **A6 (ungroundedness is positive) is an added premise** |

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

## Gödel's ontological argument (Scott's version), and its repair

Files: `GodelScott.lean`, `GodelAnderson.lean`, `GodelGrounding.lean`.
Semantics: Kripke models with constant domain, intensional properties,
world-indexed positivity. Frame conditions are hypotheses of individual
theorems; each signature shows exactly which it uses. They are the
core/mathlib relation classes passed as explicit hypotheses: `Std.Refl R`
(T), `Std.Symm R` (B), `IsTrans W R` (4).

### (i) What Lean verifies

| Theorem | Statement | Frame |
|---|---|---|
| `positive_possible` | P(φ) → ◇∃x φ(x) | K |
| `godlike_essence` | G(x) → G ess x | K |
| `godlike_unique` | at most one God-like being per world | K |
| `positive_iff_godlike_has` | P(φ) ↔ φ(g) for the God-like g | K |
| `godlike_exists` | ∃x G(x) | KB |
| `godlike_necessary` | □∃x G(x) | KB |
| `collapse_of_scott_essence` | any necessarily instantiated Scott-essence forces p → □p | K, no positivity axioms |
| `modal_collapse` | p → □p for every p | KB |
| `scott_consistent` | Scott's axioms have a model | — |
| `godel_inconsistent` | Gödel's 1970 axioms (D2 without φ(x)) prove ⊥ | KB |
| `godel_inconsistent_K` | the same, with no frame condition | K |
| `godlikeA_necessary` | Anderson: □∃x G*(x) | S5 |
| `godlikeA_unique` | Anderson: at most one God-like* being per world | T |
| `anderson_no_collapse` | an S5 model of Anderson's axioms where p → □p fails | — |
| `godlike_ne_firstPrinciple` | a model of Scott's axioms and the grounding axioms where the God-like being is not the first principle | — |
| `godlike_firstPrinciple` | with A6 (ungroundedness is positive) the God-like being is the first principle | — |

Symmetry is used exactly once in the Scott development (`godlike_exists`;
`godlike_necessary` and `modal_collapse` inherit it from there).
Reflexivity and transitivity are not used. Gödel's 1970 axioms need no frame
condition at all to be inconsistent: in `godel_inconsistent` symmetry only
supplies a world accessible from the witness world, and A1 with A2 already
give every world one (T1 applied to A3 there). Anderson's proofs use all
three conditions: reflexivity in `godlikeA_essence` (→), `godlikeA_exists`
and `godlikeA_unique`; symmetry and transitivity in `godlikeA_essence` (←),
through the stability of `P` and `□` along `R`. Whether T2* can be proved
from fewer is not tested here.

Modal collapse is caused by D2: Scott's essence quantifies over all
properties, including world-constant ones. `collapse_of_scott_essence` derives
collapse from D2 alone given one necessarily instantiated essence; A1–A5 and
symmetry merely supply that instance. Removing A4 or A5 removes T3 as well.
Anderson blocks the collapse by making D2 a biconditional on *necessary*
properties and weakening A1 to one direction; the price is bivalence of
positivity, contingent indifferent properties of the God-like being, and S5.

Field-deletion check on Anderson's axioms (the mechanical form of Hájek's
redundancy question; his results themselves are not re-checked): deleting any
one of A1–A5 from `AndersonTheory` breaks `godlikeA_necessary` as these
proofs stand. A1, A2 and A3 enter only through `godlikeA_possible` (C*), A4
only through `P_stable` and `godlikeA_essence`, A5 only in `godlikeA_exists`
and `godlikeA_necessary`. `godlikeA_unique` uses no axiom field, only D1* and
reflexivity. This shows which fields these proofs use, not that no other
proof avoids one.

`#print axioms` (Lean v4.35.0, mathlib v4.35.0):

```
'Neoplatonic.Godel.positive_possible_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'Neoplatonic.Godel.positive_possible' depends on axioms: [propext, Classical.choice, Quot.sound]
'Neoplatonic.Godel.positive_iff_godlike_has' depends on axioms: [propext, Classical.choice, Quot.sound]
'Neoplatonic.Godel.godlike_essence' depends on axioms: [propext, Classical.choice, Quot.sound]
'Neoplatonic.Godel.godlike_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'Neoplatonic.Godel.godlike_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'Neoplatonic.Godel.godlike_necessary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Neoplatonic.Godel.collapse_of_scott_essence' does not depend on any axioms
'Neoplatonic.Godel.modal_collapse' depends on axioms: [propext, Classical.choice, Quot.sound]
'Neoplatonic.Godel.scott_consistent' does not depend on any axioms
'Neoplatonic.Godel.godel_inconsistent' depends on axioms: [propext, Classical.choice, Quot.sound]
'Neoplatonic.Godel.godel_inconsistent_K' depends on axioms: [propext, Classical.choice, Quot.sound]
'Neoplatonic.Godel.godlikeA_essence' does not depend on any axioms
'Neoplatonic.Godel.godlikeA_necessary' depends on axioms: [propext, Classical.choice, Quot.sound]
'Neoplatonic.Godel.godlikeA_unique' does not depend on any axioms
'Neoplatonic.Godel.anderson_no_collapse' does not depend on any axioms
'Neoplatonic.Godel.godlike_firstPrinciple' depends on axioms: [propext, Classical.choice, Quot.sound]
'Neoplatonic.Godel.godlike_ne_firstPrinciple' depends on axioms: [propext, Classical.choice, Quot.sound]
'Neoplatonic.Godel.firstPrinciple_not_godlike' does not depend on any axioms
```

`Classical.choice` enters through `by_contra` in T1 and L. The collapse
lemma, Anderson's T2* and monotheism*, and the countermodels are constructive.

### (ii) The premises, and why a skeptic rejects them

A1–A5 are fields of a structure. Lean does not check them; it checks what
follows from them. `positive_iff_godlike_has` shows that under A1 and A3 the
positive properties are exactly the properties of the God-like being, so the
notion "positive" carries no independent content: A3 names a bearer and A1
reads positivity off it. A2 (closure under necessary entailment) and A4
(necessity of positivity) are the modal load-bearing walls; without A4 the
argument stops at ◇∃G. A5 (necessary existence is positive) is the premise
Kant's objection targets. The constant-domain semantics makes "existence" in
T3 mean "some individual is God-like at every world", not domain membership.

### (iii) The gap

A God-like being here is an element of α satisfying D1 (or D1*). The
development contains no predicate for consciousness, will, goodness, mercy,
or worship-worthiness, and no model distinguishes a God-like being from an
abstract object. Reaching any of those needs premises of the form "φ is
positive" for each φ wanted (A3's shape, repeated), and A1 then forbids
their negations. Which properties are positive is stipulated, not derived.
`[GAP]` marks each place the code stops short.

`[GAP]` Fitting (2002) repairs the collapse differently, by restricting D2's
∀ψ to extensional (rigid) properties `α → Prop`, which excludes `λy. p`. In
constant-domain semantics that makes ∃y φ(y) world-independent for such φ and
trivializes NE, so a faithful version needs varying domains with an existence
predicate `E : α → W → Prop`. Neither Fitting's variant nor any
varying-domain version is formalized here.

### Relation to the grounding framework

Independent. `godlike_ne_firstPrinciple` exhibits a model satisfying both
axiom sets in which the God-like being and the first principle are different
objects. `firstPrinciple_not_godlike` shows the converse failure. They
coincide only under A6 (being ungrounded is positive), a premise of A3's
shape that neither tradition supplies. `Modal.lean`'s two-world toy is a
special case of this.

### References

- Gödel, "Ontological Proof" (1970), *Collected Works* III (1995), with
  R. M. Adams's introductory note.
- Scott's 1972 notes, reproduced in Sobel (below).
- Sobel, J. H., "Gödel's Ontological Proof", in *On Being and Saying* (1987);
  *Logic and Theism* (2004). First statement of the collapse.
- Anderson, C. A., "Some Emendations of Gödel's Ontological Proof",
  *Faith and Philosophy* 7 (1990).
- Hájek, P., "Magari and others on Gödel's ontological proof" (1996);
  "A new small emendation of Gödel's ontological proof", *Studia Logica* 71
  (2002).
- Fitting, M., *Types, Tableaus, and Gödel's God* (2002).
- Benzmüller, C., Woltzenlogel Paleo, B., "Automating Gödel's Ontological
  Proof of God's Existence with Higher-order Automated Theorem Provers",
  ECAI 2014.
- Benzmüller, Woltzenlogel Paleo, "The Inconsistency in Gödel's Ontological
  Argument", IJCAI 2016.
- Fuenmayor, D., Benzmüller, C., "Types, Tableaus and Gödel's God in
  Isabelle/HOL", Archive of Formal Proofs (2017).
- Benzmüller, Fuenmayor, "Computer-supported Analysis of Positive Properties,
  Ultrafilters and Modal Collapse in Variants of Gödel's Ontological
  Argument", *Bulletin of the Section of Logic* 49 (2020).

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
lake env lean Neoplatonic/GodelScott.lean
lake env lean Neoplatonic/GodelAnderson.lean
lake env lean Neoplatonic/GodelGrounding.lean
lake env lean Check.lean
```

A good next acceptance gate is to run all commands under a pinned mathlib
commit in CI, compare results to the finite audits, and inspect
`#print axioms` for the main theorems. At present, the limitations above
prevent asserting that Lean accepted the scripts.
