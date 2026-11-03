import Neoplatonic.LTR.ComplexValuedStarAlgHom

/-!
# Complex-valued Dirac commutator on one Euclidean marked edge

The Hermitian Dirac block has real mass m and coupling s. A complex
observable acts by the diagonal matrix diag(a,b), with a,b∈ℂ.

The commutator is s*(b-a) times the fixed unitary skew rotation,
and its Euclidean operator norm is |s| * ‖b-a‖. The diagonal
mass cancels, independently of the complex phases of a and b.
-/

namespace Neoplatonic.LTR

/-- Complex-valued block commutator with mass cancellation. -/
theorem complexDirac_complexObservableMatrix_commutator
    (mass scale : ℝ) (a b : ℂ) :
    complexMassDirac mass scale * complexValuedObservableMatrix a b -
      complexValuedObservableMatrix a b * complexMassDirac mass scale =
      (((scale : ℂ) * (b - a))) • complexEdgeRotationMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexMassDirac, complexValuedObservableMatrix,
      complexEdgeRotationMatrix, Matrix.mul_apply,
      Matrix.smul_apply, Fin.sum_univ_two] <;>
    push_cast <;> ring

/-- On the actual complex Euclidean Hilbert block,
the commutator is the complex edge difference times a unitary. -/
theorem complexDirac_complexObservableBlock_commutator
    (mass scale : ℝ) (a b : ℂ) :
    (complexEuclideanDiracBlock mass scale).comp
       (complexValuedObservableBlock a b) -
      (complexValuedObservableBlock a b).comp
       (complexEuclideanDiracBlock mass scale) =
      (((scale : ℂ) * (b - a))) • complexEdgeRotationCLM := by
  have h := congrArg
    (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)) A)
    (complexDirac_complexObservableMatrix_commutator mass scale a b)
  simpa [complexEuclideanDiracBlock, complexValuedObservableBlock,
    complexEdgeRotationCLM, map_mul, map_sub, map_smul,
    ContinuousLinearMap.mul_def] using h

/-- Exact complex Hilbert commutator norm for one marked edge. -/
theorem complexDirac_complexObservableBlock_commutator_norm
    (mass scale : ℝ) (a b : ℂ) :
    ‖(complexEuclideanDiracBlock mass scale).comp
       (complexValuedObservableBlock a b) -
      (complexValuedObservableBlock a b).comp
       (complexEuclideanDiracBlock mass scale)‖ =
      |scale| * ‖b - a‖ := by
  rw [complexDirac_complexObservableBlock_commutator,
    norm_smul, complexEdgeRotationCLM_norm_eq_one, mul_one]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

end Neoplatonic.LTR
