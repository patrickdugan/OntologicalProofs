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
