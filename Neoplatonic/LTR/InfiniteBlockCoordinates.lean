import Neoplatonic.LTR.HilbertResolventWeights

/-!
# Coordinate calculus for actual bounded diagonal Dirac resolvents

The bounded diagonal operator built by mathlib's lp.mapCLM
acts by scalar multiplication on each Hilbert coordinate. This gives
an exact pointwise difference identity for the full squared resolvent
and its N-th tail, with a cutoff after the first N blocks.

This module supplies the concrete map-level equality needed to
deduce compactness of the full resolvent from finite-rank cutoffs.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Scalar block-diagonal Hilbert operators act at every coordinate. -/
theorem boundedBlockDiagonal_apply
    (w : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hw : ∀ j, |w j| ≤ K)
    (ψ : DiracBlockHilbert) (j : ℕ) :
    boundedBlockDiagonal w K hK hw ψ j = w j • ψ j := by
  change scalarBlockCLM (w j) (ψ j) = w j • ψ j
  simp [scalarBlockCLM]

/-- Exact coefficient identity for the infinite squared resolvent. -/
theorem chosenSquaredResolventCLM_apply
    (scale : ℕ → ℝ) (ψ : DiracBlockHilbert) (j : ℕ) :
    chosenSquaredResolventCLM scale ψ j =
      chosenSquaredResolventWeight scale j • ψ j := by
  exact boundedBlockDiagonal_apply _ _ _ _ ψ j

/-- Exact coefficient identity for the N-th squared-resolvent tail. -/
theorem chosenSquaredResolventTailCLM_apply
    (scale : ℕ → ℝ) (N : ℕ)
    (ψ : DiracBlockHilbert) (j : ℕ) :
    chosenSquaredResolventTailCLM scale N ψ j =
      chosenSquaredResolventTailWeight scale N j • ψ j := by
  exact boundedBlockDiagonal_apply _ _ _ _ ψ j

/-- The complementary finite-cutoff Hilbert operator is supported
only in the first N two-dimensional blocks. -/
theorem squaredResolventCutoff_apply
    (scale : ℕ → ℝ) (N : ℕ)
    (ψ : DiracBlockHilbert) (j : ℕ) :
    (chosenSquaredResolventCLM scale -
      chosenSquaredResolventTailCLM scale N) ψ j =
    if j < N then chosenSquaredResolventWeight scale j • ψ j
      else 0 := by
  rw [ContinuousLinearMap.sub_apply, lp.sub_apply,
    chosenSquaredResolventCLM_apply,
    chosenSquaredResolventTailCLM_apply]
  by_cases hj : j < N
  · have hn : ¬ N ≤ j := by omega
    simp [chosenSquaredResolventTailWeight, hn, hj]
  · have hn : N ≤ j := Nat.le_of_not_gt hj
    simp [chosenSquaredResolventTailWeight, hn, hj]

end Neoplatonic.LTR
