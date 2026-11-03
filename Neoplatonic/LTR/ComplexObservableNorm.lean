import Neoplatonic.LTR.ComplexObservableBlocks
import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Exact operator norm of a two-point complex Dirac commutator

The 2×2 commutator is a real scalar multiple of the fixed unitary
rotation J = [[0,1],[-1,0]]. Its scalar is scale*(b-a). Since J is a
unitary complex-linear operator on EuclideanSpace ℂ (Fin 2), its norm
is exactly one, so the commutator norm is |scale*(b-a)|.

All statements concern the genuine continuous linear maps that occur
as blocks of the infinite Dirac representation.
-/

namespace Neoplatonic.LTR

/-- Fixed skew rotation on the complex Euclidean two-vector. -/
def complexEdgeRotationMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; -1, 0]

/-- The edge rotation is unitary at matrix level. -/
theorem complexEdgeRotationMatrix_star_mul_self :
    star complexEdgeRotationMatrix * complexEdgeRotationMatrix =
      (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexEdgeRotationMatrix, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two]

/-- The unitary rotation as a genuine bounded complex Euclidean operator. -/
noncomputable def complexEdgeRotationCLM :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
    complexEdgeRotationMatrix

/-- The rotation is unitary as an operator. -/
theorem complexEdgeRotationCLM_star_mul_self :
    star complexEdgeRotationCLM * complexEdgeRotationCLM =
      (1 : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) := by
  have h := congrArg
    (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)) A)
    complexEdgeRotationMatrix_star_mul_self
  simpa [complexEdgeRotationCLM, map_mul, map_star,
    ContinuousLinearMap.mul_def] using h

/-- The fixed complex Euclidean edge rotation has exact norm one. -/
theorem complexEdgeRotationCLM_norm_eq_one :
    ‖complexEdgeRotationCLM‖ = 1 := by
  have h : ‖complexEdgeRotationCLM‖ * ‖complexEdgeRotationCLM‖ = 1 := by
    rw [← CStarRing.norm_star_mul_self,
      complexEdgeRotationCLM_star_mul_self]
    simp
  nlinarith [norm_nonneg complexEdgeRotationCLM]

/-- The exact commutator is a real scalar multiple of a unitary rotation. -/
theorem complexObservableBlock_commutator_eq_smul_rotation
    (mass scale a b : ℝ) :
    (complexEuclideanDiracBlock mass scale).comp (complexObservableBlock a b) -
      (complexObservableBlock a b).comp (complexEuclideanDiracBlock mass scale) =
      ((scale * (b - a) : ℝ) : ℂ) • complexEdgeRotationCLM := by
  rw [complexObservableBlock_commutator]
  change (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
    (!![0, ((scale * (b - a) : ℝ) : ℂ);
        ((scale * (a - b) : ℝ) : ℂ), 0]) =
    ((scale * (b - a) : ℝ) : ℂ) •
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
        complexEdgeRotationMatrix
  rw [← map_smul]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexEdgeRotationMatrix] <;> push_cast <;> ring

/-- The exact Euclidean commutator norm is the absolute edge quotient. -/
theorem complexObservableBlock_commutator_norm
    (mass scale a b : ℝ) :
    ‖(complexEuclideanDiracBlock mass scale).comp (complexObservableBlock a b) -
       (complexObservableBlock a b).comp (complexEuclideanDiracBlock mass scale)‖ =
      |scale * (b - a)| := by
  rw [complexObservableBlock_commutator_eq_smul_rotation,
    norm_smul, complexEdgeRotationCLM_norm_eq_one, mul_one]
  exact (Complex.norm_real (scale * (b - a))).trans
    (Real.norm_eq_abs _)

end Neoplatonic.LTR
