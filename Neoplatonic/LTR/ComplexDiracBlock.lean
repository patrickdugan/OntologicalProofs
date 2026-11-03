import Neoplatonic.LTR.InfiniteSquaredResolventIdentity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Complex Dirac blocks for a genuine complex Hilbert-space realization

The real parameters m,s define a Hermitian complex two-point matrix
  [[m,s],[s,-m]]
and a self-adjoint continuous complex-linear Euclidean block operator.
The squared block is scalar with coefficient m²+s².
-/ 

namespace Neoplatonic.LTR

/-- Hermitian complex two-point Dirac matrix with real mass and coupling. -/
def complexMassDirac (mass scale : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(mass : ℂ), (scale : ℂ); (scale : ℂ), -(mass : ℂ)]

/-- The complex Dirac matrix has a scalar square. -/
theorem complexMassDirac_square (mass scale : ℝ) :
    complexMassDirac mass scale * complexMassDirac mass scale =
      (((mass ^ 2 + scale ^ 2 : ℝ) : ℂ)) •
        (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexMassDirac, Matrix.mul_apply, Fin.sum_univ_two] <;>
    push_cast <;> ring

/-- Every complex mass-shifted Dirac block is Hermitian. -/
theorem complexMassDirac_isHermitian (mass scale : ℝ) :
    (complexMassDirac mass scale).IsHermitian := by
  change (complexMassDirac mass scale).conjTranspose =
    complexMassDirac mass scale
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [complexMassDirac, Matrix.conjTranspose_apply] <;> ring

/-- Complex two-component Hilbert-space Dirac block. -/
noncomputable def complexEuclideanDiracBlock (mass scale : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
    (complexMassDirac mass scale)

/-- A genuine self-adjoint complex-linear Euclidean block. -/
theorem complexEuclideanDiracBlock_isSelfAdjoint (mass scale : ℝ) :
    IsSelfAdjoint (complexEuclideanDiracBlock mass scale) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  have h : ((complexMassDirac mass scale).toEuclideanLin).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (complexMassDirac_isHermitian mass scale)
  simpa only [complexEuclideanDiracBlock,
    Matrix.coe_toEuclideanCLM_eq_toEuclideanLin] using h

/-- The self-adjoint complex Dirac operator's square is the real scalar μ². -/
theorem complexEuclideanDiracBlock_square
    (mass scale : ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    complexEuclideanDiracBlock mass scale
      (complexEuclideanDiracBlock mass scale v) =
    (((mass ^ 2 + scale ^ 2 : ℝ) : ℂ)) • v := by
  have h := congrArg
    (fun A : Matrix (Fin 2) (Fin 2) ℂ =>
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) A) v)
    (complexMassDirac_square mass scale)
  simpa [complexEuclideanDiracBlock, map_mul, map_smul] using h

end Neoplatonic.LTR
