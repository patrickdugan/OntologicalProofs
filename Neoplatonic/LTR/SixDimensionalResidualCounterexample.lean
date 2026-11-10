import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# LTR-MAN-57: a six-dimensional residual product survives spectral contractions

The five-dimensional zero-product argument has a genuine
dimension-sensitive step. With four signed extremal eigendirections
in dimension six, a two-dimensional residual block remains.

This module gives a fully explicit pair of Hermitian traceless
six-by-six matrices with operator norms one, both sum/difference
operator norms at most one, and a nonzero ordered product.
On the residual pair the matrices are the same small signed
diagonal operator, while each has its independent ±1 extremal pair.

This is a counterexample to extending the *abstract* spectral
zero-product deduction to dimension six from selfadjointness, trace,
norm-one and sum/difference contractions alone. It does not assert
a six-dimensional realization of the Hamming Connes metric.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Signed A coordinate weights: extremal +1,-1 and a small
traceless two-dimensional residual pair. -/
def sixResidualAWeight (i : Fin 6) : ℂ :=
  if i = 0 then 1 else if i = 1 then -1
  else if i = 4 then (1/4 : ℂ)
  else if i = 5 then (-1/4 : ℂ) else 0

/-- Signed B coordinate weights: disjoint extremal +1,-1 and
the same small traceless residual pair. -/
def sixResidualBWeight (i : Fin 6) : ℂ :=
  if i = 2 then 1 else if i = 3 then -1
  else if i = 4 then (1/4 : ℂ)
  else if i = 5 then (-1/4 : ℂ) else 0

def sixResidualA : SixMat := Matrix.diagonal sixResidualAWeight
def sixResidualB : SixMat := Matrix.diagonal sixResidualBWeight

/-- The two coordinate operators are Hermitian. -/
theorem sixResidualA_selfAdjoint : IsSelfAdjoint sixResidualA := by
  apply Matrix.IsHermitian.isSelfAdjoint
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  fin_cases i <;> simp [sixResidualA, sixResidualAWeight, IsSelfAdjoint]

theorem sixResidualB_selfAdjoint : IsSelfAdjoint sixResidualB := by
  apply Matrix.IsHermitian.isSelfAdjoint
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  fin_cases i <;> simp [sixResidualB, sixResidualBWeight, IsSelfAdjoint]

/-- Each has zero trace, including the residual ±1/4 pair. -/
theorem sixResidualA_trace_zero : sixResidualA.trace = 0 := by
  simp [sixResidualA, Matrix.trace_diagonal,
    Fin.sum_univ_six, sixResidualAWeight]

theorem sixResidualB_trace_zero : sixResidualB.trace = 0 := by
  simp [sixResidualB, Matrix.trace_diagonal,
    Fin.sum_univ_six, sixResidualBWeight]

/-- Both six-dimensional Hermitian matrices have operator norm one. -/
theorem sixResidualA_norm_one : ‖sixResidualA‖ = 1 := by
  change ‖Matrix.diagonal sixResidualAWeight‖ = 1
  rw [Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    fin_cases i <;> norm_num [sixResidualAWeight]
  · have h := norm_le_pi_norm sixResidualAWeight (0 : Fin 6)
    simpa [sixResidualAWeight] using h

theorem sixResidualB_norm_one : ‖sixResidualB‖ = 1 := by
  change ‖Matrix.diagonal sixResidualBWeight‖ = 1
  rw [Matrix.l2_opNorm_diagonal]
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    fin_cases i <;> norm_num [sixResidualBWeight]
  · have h := norm_le_pi_norm sixResidualBWeight (2 : Fin 6)
    simpa [sixResidualBWeight] using h

/-- The opposite-witness sum is a true Hilbert operator contraction. -/
theorem sixResidual_sum_contraction :
    ‖sixResidualA + sixResidualB‖ ≤ 1 := by
  have heq :
      sixResidualA + sixResidualB =
        Matrix.diagonal (fun i => sixResidualAWeight i + sixResidualBWeight i) := by
    ext i j
    simp [sixResidualA, sixResidualB, Matrix.diagonal_apply]
  rw [heq, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  fin_cases i <;> norm_num [sixResidualAWeight, sixResidualBWeight]

/-- The other opposite-witness difference is also a contraction. -/
theorem sixResidual_difference_contraction :
    ‖sixResidualA - sixResidualB‖ ≤ 1 := by
  have heq :
      sixResidualA - sixResidualB =
        Matrix.diagonal (fun i => sixResidualAWeight i - sixResidualBWeight i) := by
    ext i j
    simp [sixResidualA, sixResidualB, Matrix.diagonal_apply]
  rw [heq, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  fin_cases i <;> norm_num [sixResidualAWeight, sixResidualBWeight]

/-- Both ordered products have nonzero residual action at coordinate four. -/
theorem sixResidual_product_nonzero :
    sixResidualA * sixResidualB ≠ 0 ∧
      sixResidualB * sixResidualA ≠ 0 := by
  constructor
  · intro h
    have he := congrArg (fun M : SixMat => M 4 4) h
    simp [sixResidualA, sixResidualB, Matrix.diagonal_mul_diagonal,
      sixResidualAWeight, sixResidualBWeight] at he
  · intro h
    have he := congrArg (fun M : SixMat => M 4 4) h
    simp [sixResidualA, sixResidualB, Matrix.diagonal_mul_diagonal,
      sixResidualAWeight, sixResidualBWeight] at he

/-- Counterexample to a dimension-independent graded-style zero-product
deduction from the basic operator-norm and trace hypotheses. -/
theorem sixDim_spectralHypotheses_doNotForce_zeroProducts :
    ∃ A B : SixMat,
      IsSelfAdjoint A ∧ IsSelfAdjoint B ∧
      A.trace = 0 ∧ B.trace = 0 ∧
      ‖A‖ = 1 ∧ ‖B‖ = 1 ∧
      ‖A + B‖ ≤ 1 ∧ ‖A - B‖ ≤ 1 ∧
      A * B ≠ 0 ∧ B * A ≠ 0 := by
  exact ⟨sixResidualA, sixResidualB,
    sixResidualA_selfAdjoint, sixResidualB_selfAdjoint,
    sixResidualA_trace_zero, sixResidualB_trace_zero,
    sixResidualA_norm_one, sixResidualB_norm_one,
    sixResidual_sum_contraction, sixResidual_difference_contraction,
    sixResidual_product_nonzero.1, sixResidual_product_nonzero.2⟩

end Neoplatonic.LTR
