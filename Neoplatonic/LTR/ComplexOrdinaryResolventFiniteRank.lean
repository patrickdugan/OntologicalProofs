import Neoplatonic.LTR.ComplexOrdinaryResolventGlobal
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Genuine finite-rank truncations of the ordinary complex Dirac resolvent

The bounded full complex resolvent Q is a direct sum of two-dimensional
blocks Q_j. Each single-coordinate map factors through a finite-dimensional
Euclidean space and is compact. Finite sums yield compact rank-2N cutoffs
that retain only the first N blocks of Q.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- The finite-rank complex Hilbert operator supported at one index. -/
noncomputable def complexSingleOrdinaryResolventBlock
    (scale : ℕ → ℝ) (j : ℕ) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  ((lp.singleContinuousLinearMap ℂ
      (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j).comp
        (complexOrdinaryResolventBlock scale j)).comp
    (lp.evalCLM ℂ (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j)

/-- Each single-coordinate ordinary resolvent block is compact. -/
theorem complexSingleOrdinaryResolventBlock_compact
    (scale : ℕ → ℝ) (j : ℕ) :
    IsCompactOperator (complexSingleOrdinaryResolventBlock scale j) := by
  have hev : IsCompactOperator
      (lp.evalCLM ℂ (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  unfold complexSingleOrdinaryResolventBlock
  exact hev.clm_comp
    ((lp.singleContinuousLinearMap ℂ
      (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j).comp
        (complexOrdinaryResolventBlock scale j))

/-- First N ordinary-resolvent blocks as an actual bounded Hilbert map. -/
noncomputable def finiteComplexOrdinaryResolvent
    (scale : ℕ → ℝ) (N : ℕ) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  ∑ j ∈ Finset.range N, complexSingleOrdinaryResolventBlock scale j

/-- Each truncated ordinary resolvent is compact, with rank ≤2N. -/
theorem finiteComplexOrdinaryResolvent_compact
    (scale : ℕ → ℝ) (N : ℕ) :
    IsCompactOperator (finiteComplexOrdinaryResolvent scale N) := by
  classical
  unfold finiteComplexOrdinaryResolvent
  induction Finset.range N using Finset.induction_on with
  | empty =>
      simpa using
        (isCompactOperator_zero
          (M₁ := ComplexDiracBlockHilbert) (M₂ := ComplexDiracBlockHilbert))
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact (complexSingleOrdinaryResolventBlock_compact scale j).add ih

/-- Exact coordinate formula for finite ordinary-resolvent truncation. -/
theorem finiteComplexOrdinaryResolvent_apply
    (scale : ℕ → ℝ) (N : ℕ)
    (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    (finiteComplexOrdinaryResolvent scale N ψ) j =
      if j < N then complexOrdinaryResolventBlock scale j (ψ j)
      else 0 := by
  classical
  have hsum :
      finiteComplexOrdinaryResolvent scale N ψ =
      ∑ i ∈ Finset.range N,
        lp.single 2 i (complexOrdinaryResolventBlock scale i (ψ i)) := by
    simp [finiteComplexOrdinaryResolvent, complexSingleOrdinaryResolventBlock,
      lp.evalCLM, lp.evalₗ] <;> rfl
  rw [hsum]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
  simp [Finset.sum_pi_single, Finset.mem_range]

end Neoplatonic.LTR
