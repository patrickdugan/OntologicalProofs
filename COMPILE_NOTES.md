# Compile notes (Lean v4.35.0, current mathlib, 2026-10-17)
All 10 modules now compile; no `sorry`. Main theorems depend only on propext, Classical.choice, Quot.sound.
Fixes made to the original files:
- Moved `import` lines above the module docstrings (all files).
- Core.lean: `refl` pattern takes no args; uniqueness step used `ancestor_of_root_eq hroot (hy.2 root)`.
- Amalgamation.lean: rewrote induction patterns (`refl`, `@step y w ...`) in `root_ancestors_agree`.
- LocalConfluence.lean: renamed variable `local` (reserved word) to `lc`; fixed `refl`/`@step` patterns.
Assumptions unchanged: commonEffect / localCoherence / singleParent and the RH bridge
`spectralAlignmentToCommonPrior` are still hypotheses, not theorems.

## Arithmetic patch (2026-10-17)
Added `Neoplatonic/Arithmetic.lean` and the RH.lean vacuity lemmas. Compile fixes: `mul_eq_left.mp h.symm`; explicit product hint in `reach₂_mul_right`; zeta/Möbius statements written with `ArithmeticFunction.zeta`/`moebius` explicitly. All theorems depend only on propext / Classical.choice / Quot.sound.

## Gödel/Scott/Anderson patch (2026-10-18)
Added `GodelScott.lean`, `GodelAnderson.lean`, `GodelGrounding.lean` (handoff `GODEL_SPEC.md`, written
without a compiler), wired into `Neoplatonic.lean` and `Check.lean`; `Modal.lean` gains a pointer comment.
`lake build Neoplatonic` succeeds; no `sorry`, no `axiom` declarations. The only warning on the new files
is mathlib's header linter (`Copyright too short!`), which every existing module also triggers.

No logical error was found in the handoff, and no statement was weakened. Fixes, with the error text:

1. **Frame conditions.** This mathlib has removed `Reflexive` and `Transitive` and deprecated `Symmetric`:
   `` warning: `Symmetric` has been deprecated: Use `Std.Symm` instead ``
   (and `Reflexive R` / `Transitive R` no longer resolve). Replaced by the library classes, still passed as
   explicit hypotheses so each signature shows what it consumes: `Std.Refl R`, `Std.Symm R`, `IsTrans W R`.
   Uses change accordingly: `hsymm hwv` → `hsymm.symm _ _ hwv`, `hrefl v` → `hrefl.refl v`,
   `htrans a b` → `htrans.trans _ _ _ a b`; `totalR_refl/symm/trans` and the symmetry proof in
   `godlike_ne_firstPrinciple` become anonymous constructors `⟨fun ... => trivial⟩`.
2. **`modal_collapse`** lost its theory argument:
   `` error(lean.unknownIdentifier): Unknown identifier `T` ``
   Its statement never mentions the section variable `T`, and Lean includes section variables in a theorem
   only when the statement mentions them (bodies don't count). Added `include T in`; the signature is now
   `modal_collapse T hsymm w p hp`, as the handoff intended.
3. **`godlike_ne_firstPrinciple`**: `⟨fun ⟨_, hy⟩ => nomatch hy.2, reach_false_all⟩` parses as a
   two-discriminant `nomatch hy.2, reach_false_all`:
   `` error: Insufficient number of fields for `⟨...⟩` constructor: Constructor `And.intro` has 2 explicit field, but only 1 was provided ``
   Parenthesized the lambda.
4. **`andersonTwoWorlds.A3`**: unused binder `φ` (`Variable name φ is not explicitly referenced`); now `_`.

Pitfalls 1, 2 and 4–8 in the spec did not occur: `Box`/`Dia` work as plain `def`s, the `where`-block
lambdas elaborate as written, both `▸` uses go through, `nomatch` on `false = true` works,
`Nat.not_lt_zero y hy` unfolds `natTheory`, and `Iff.rfl` closes A1 in all three Scott models.
Errors 2–4 were first found with a core-only harness (the modules concatenated after `Core` and `Modal`
with imports stripped, run under bare `lean`, so mathlib doesn't have to load each round); the final
results above are from the real `lake build` and `lake env lean Check.lean`.

**Addition beyond the handoff:** `godel_inconsistent_K`, Gödel-1970 ⊢ ⊥ with no frame condition. In
`godel_inconsistent` symmetry only supplies a world accessible from the witness world `v`; T1 applied to
A3 at `v` already gives one. `godel_inconsistent` is kept as specified.

**Hájek field-deletion test** (spec §3; done in the harness). Deleting one `AndersonTheory` field at a
time and listing what errors directly / what then depends on `sorryAx`:

| Deleted | Direct errors | Lost (transitively) |
|---|---|---|
| A1 | `godlikeA_possible` | `godlikeA_possible`, `godlikeA_exists`, `godlikeA_necessary` |
| A2 | `godlikeA_possible` | same as A1 |
| A3 | `godlikeA_possible` | same as A1 |
| A4 | `P_stable`, `godlikeA_essence` | `P_stable`, `godlikeA_stable`, `godlikeA_essence`, `godlikeA_exists`, `godlikeA_necessary` |
| A5 | `godlikeA_exists`, `godlikeA_necessary` | `godlikeA_exists`, `godlikeA_necessary` |

So every field is used by these proofs of T3*. That says nothing about whether a different proof could
avoid one, so Hájek's redundancy claims are not tested by this. `godlikeA_unique` uses no field at all.

Frame conditions as finally compiled: `godlike_exists`, `godlike_necessary`, `modal_collapse`,
`godel_inconsistent` take `Std.Symm R` only; `godlikeA_essence`, `godlikeA_exists`,
`godlikeA_necessary` take all three; `godlikeA_unique` takes `Std.Refl R` only; `P_stable` takes
`Std.Symm R`; `box_stable`, `godlikeA_stable` take `Std.Symm R` and `IsTrans W R`. The unused-variables
linter reports none of them unused.

`#print axioms` (from `lake env lean Check.lean`):
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
The earlier `Check.lean` lines are unchanged (`common_ground_iff_not_coprime`: `[propext, Quot.sound]`;
`six_has_incomparable_co_grounds`: `[propext]`; the rest `[propext, Classical.choice, Quot.sound]`).
