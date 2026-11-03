import Neoplatonic.LTR.ComplexCompactRealSelfAdjoint

/-!
# Complex-valued two-point observables on the Euclidean Hilbert block

For z,w∈ℂ the pointwise evaluation matrix diag(z,w) acts through
Mathlib's complex-linear matrix-to-Euclidean equivalence. This is
the algebraic complex-valued extension of the previously verified
real-observable representation. All identities are on the actual
complex 2-dimensional Hilbert space.
-/

namespace Neoplatonic.LTR

/-- The complex diagonal point-evaluation matrix for two marked endpoints. -/
def complexValuedObservableMatrix (z w : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![z, 0; 0, w]

theorem complexValuedObservableMatrix_diagonal (z w : ℂ) :
    complexValuedObservableMatrix z w =
      Matrix.diagonal (fun i : Fin 2 => if i = 0 then z else w) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexValuedObservableMatrix, Matrix.diagonal_apply]

theorem complexValuedObservableMatrix_mul (a b c d : ℂ) :
    complexValuedObservableMatrix a b * complexValuedObservableMatrix c d =
      complexValuedObservableMatrix (a * c) (b * d) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexValuedObservableMatrix, Matrix.mul_apply,
      Fin.sum_univ_two]

theorem complexValuedObservableMatrix_add (a b c d : ℂ) :
    complexValuedObservableMatrix (a + c) (b + d) =
      complexValuedObservableMatrix a b + complexValuedObservableMatrix c d := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexValuedObservableMatrix]

theorem complexValuedObservableMatrix_star (a b : ℂ) :
    star (complexValuedObservableMatrix a b) =
      complexValuedObservableMatrix (star a) (star b) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexValuedObservableMatrix,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

theorem complexValuedObservableMatrix_one :
    complexValuedObservableMatrix 1 1 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexValuedObservableMatrix, Matrix.one_apply]

/-- Continuous complex-linear Hilbert block for two complex endpoint values. -/
noncomputable def complexValuedObservableBlock (z w : ℂ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
    (complexValuedObservableMatrix z w)

theorem complexValuedObservableBlock_norm_le
    (a b : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) :
    ‖complexValuedObservableBlock a b‖ ≤ M := by
  change ‖(Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
    (complexValuedObservableMatrix a b)‖ ≤ M
  rw [Matrix.l2_opNorm_toEuclideanCLM,
    complexValuedObservableMatrix_diagonal,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg hM).mpr
  intro i
  fin_cases i
  · simpa using ha
  · simpa using hb

theorem complexValuedObservableBlock_mul (a b c d : ℂ) :
    (complexValuedObservableBlock a b).comp
      (complexValuedObservableBlock c d) =
    complexValuedObservableBlock (a * c) (b * d) := by
  have h := congrArg
    (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)) A)
    (complexValuedObservableMatrix_mul a b c d)
  change ((Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
      (complexValuedObservableMatrix a b)).comp
    ((Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
      (complexValuedObservableMatrix c d)) =
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
      (complexValuedObservableMatrix (a * c) (b * d))
  rw [← ContinuousLinearMap.mul_def]
  simpa only [map_mul] using h

theorem complexValuedObservableBlock_add (a b c d : ℂ) :
    complexValuedObservableBlock (a + c) (b + d) =
      complexValuedObservableBlock a b +
      complexValuedObservableBlock c d := by
  have h := congrArg
    (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)) A)
    (complexValuedObservableMatrix_add a b c d)
  simpa [complexValuedObservableBlock, map_add] using h

theorem complexValuedObservableBlock_one :
    complexValuedObservableBlock 1 1 =
      ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)) := by
  change (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
    (complexValuedObservableMatrix 1 1) =
    ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2))
  rw [complexValuedObservableMatrix_one]
  exact map_one _

theorem complexValuedObservableBlock_star (a b : ℂ) :
    star (complexValuedObservableBlock a b) =
      complexValuedObservableBlock (star a) (star b) := by
  have h := congrArg
    (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)) A)
    (complexValuedObservableMatrix_star a b)
  simpa [complexValuedObservableBlock, map_star] using h

end Neoplatonic.LTR
