import Neoplatonic.LTR.InfiniteBlockCoordinates
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Finite-rank approximants of the infinite squared-resolvent operator

The j-th block of the Hilbert squared-resolvent is a continuous
linear map from the Hilbert sum to the finite-dimensional j-th
Euclidean coordinate, followed by scalar multiplication and insertion
back into the Hilbert sum.

The evaluation map into a locally compact finite-dimensional range is
compact. Composing it with bounded block operations remains compact.
Every finite sum of such block maps is a compact operator.

This module constructs *actual* finite-rank Hilbert operators rather
than assuming their existence. The exact identity with the finite
cutoff of the squared resolvent is checked separately.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- The j-th two-dimensional Hilbert block as a bounded map H→H. -/
noncomputable def singleSquaredResolventBlock
    (scale : ℕ → ℝ) (j : ℕ) :
    DiracBlockHilbert →L[ℝ] DiracBlockHilbert :=
  ((lp.singleContinuousLinearMap ℝ
      (fun _ : ℕ => EuclideanSpace ℝ (Fin 2)) 2 j).comp
        (scalarBlockCLM (chosenSquaredResolventWeight scale j))).comp
    (lp.evalCLM ℝ (fun _ : ℕ => EuclideanSpace ℝ (Fin 2)) 2 j)

/-- Every single block operator is compact because its evaluation
has finite-dimensional range. -/
theorem singleSquaredResolventBlock_compact
    (scale : ℕ → ℝ) (j : ℕ) :
    IsCompactOperator (singleSquaredResolventBlock scale j) := by
  have hev : IsCompactOperator
      (lp.evalCLM ℝ (fun _ : ℕ => EuclideanSpace ℝ (Fin 2)) 2 j) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  unfold singleSquaredResolventBlock
  exact hev.clm_comp
    ((lp.singleContinuousLinearMap ℝ
      (fun _ : ℕ => EuclideanSpace ℝ (Fin 2)) 2 j).comp
        (scalarBlockCLM (chosenSquaredResolventWeight scale j)))

/-- Finite sum of the first N squared-resolvent block operators. -/
noncomputable def finiteSquaredResolvent
    (scale : ℕ → ℝ) (N : ℕ) :
    DiracBlockHilbert →L[ℝ] DiracBlockHilbert :=
  ∑ j ∈ Finset.range N, singleSquaredResolventBlock scale j

/-- Every truncated resolvent is compact as a finite sum of compact
two-dimensional block maps. -/
theorem finiteSquaredResolvent_compact
    (scale : ℕ → ℝ) (N : ℕ) :
    IsCompactOperator (finiteSquaredResolvent scale N) := by
  classical
  unfold finiteSquaredResolvent
  induction Finset.range N using Finset.induction_on with
  | empty =>
      simpa using
        (isCompactOperator_zero
          (M₁ := DiracBlockHilbert) (M₂ := DiracBlockHilbert))
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact (singleSquaredResolventBlock_compact scale j).add ih

end Neoplatonic.LTR
