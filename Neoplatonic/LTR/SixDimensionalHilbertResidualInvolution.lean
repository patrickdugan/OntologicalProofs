import Neoplatonic.LTR.SixDimensionalExactHammingResidualInvolution
import Neoplatonic.LTR.SixDimensionalMixedTraceBridge
import Mathlib.Tactic

/-!
# LTR-MAN-90: lift a residual Pauli involution into the true Hilbert operator

The true residual Pauli matrices of MAN-65 are the image of the
compressed Hilbert operators under a single isometric orthonormal
basis conjugation and Mathlib's matrix-C* algebra equivalence.

Both transformations preserve multiplication and are injective.
An involution of the represented 2×2 matrix is therefore an
involution of the *actual compressed bounded Hilbert operator*.

This module carries the MAN-89 sum/difference residual involutions
back to the original complex two-dimensional residual submodule.
No abstract matrix eigenvector replacement is involved.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev TwoH := EuclideanSpace ℂ (Fin 2)

/-- The faithful complex 2×2 C*-matrix representation carries
square-one equations backwards to the underlying Euclidean
continuous linear Hilbert operator. -/
theorem twoEuclideanCstarMatrix_involution_lift
    (T : TwoH →L[ℂ] TwoH)
    (h : twoEuclideanCstarMatrix T *
      twoEuclideanCstarMatrix T = 1) :
    T * T = 1 := by
  let F := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)
  have h' : F.symm (T * T) = F.symm (1 : TwoH →L[ℂ] TwoH) := by
    simpa only [twoEuclideanCstarMatrix, map_mul, map_one] using h
  exact F.symm.injective h'

/-- A unitary Hilbert basis change reflects square-one equations.
This is an operator identity, with no norm or trace approximations. -/
theorem hilbertIsometricConjugate_involution_lift
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E)
    (h : hilbertIsometricConjugate U T *
      hilbertIsometricConjugate U T = 1) :
    T * T = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg
    (fun R : F →L[ℂ] F => R (U x)) h
  change U (T (T (U.symm (U x)))) = U x at hx
  change T (T x) = x
  exact U.injective (by simpa using hx)

/-- A genuine six-dimensional extremal system whose two
residual Pauli matrices have involutive sum has a square-one
SUM of the original residual bounded Hilbert operators. -/
theorem TwoDirectionExtremalSystem.residualPlus_involution_of_pauli
    (S : TwoDirectionExtremalSystem SixH)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hmat :
      (S.sixDimResidualMatrixA hq (by simp) +
        S.sixDimResidualMatrixB hq (by simp)) *
      (S.sixDimResidualMatrixA hq (by simp) +
        S.sixDimResidualMatrixB hq (by simp)) = 1) :
    (S.residualA + S.residualB) *
      (S.residualA + S.residualB) = 1 := by
  let T : TwoH →L[ℂ] TwoH :=
    S.sixDimEuclideanResidualA hq (by simp) +
      S.sixDimEuclideanResidualB hq (by simp)
  have hmatrix :
      twoEuclideanCstarMatrix T =
        S.sixDimResidualMatrixA hq (by simp) +
          S.sixDimResidualMatrixB hq (by simp) := by
    change twoEuclideanCstarMatrix
        (S.sixDimEuclideanResidualA hq (by simp) +
          S.sixDimEuclideanResidualB hq (by simp)) = _
    rw [twoEuclideanCstarMatrix_add]
    exact congrArg₂ (· + ·)
      (S.sixDimCstarResidualMatrixA_eq hq (by simp))
      (S.sixDimCstarResidualMatrixB_eq hq (by simp))
  have heuc : T * T = 1 := by
    apply twoEuclideanCstarMatrix_involution_lift
    rw [hmatrix]
    exact hmat
  let U := (S.sixDimResidualBasis hq (by simp)).repr
  have hconj : hilbertIsometricConjugate U
        (S.residualA + S.residualB) = T := by
    rw [hilbertIsometricConjugate_add]
    rfl
  apply hilbertIsometricConjugate_involution_lift U
  rw [hconj]
  exact heuc

/-- The analogous result for the difference of the genuine
compressed residual Hilbert coordinate operators. -/
theorem TwoDirectionExtremalSystem.residualMinus_involution_of_pauli
    (S : TwoDirectionExtremalSystem SixH)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hmat :
      (S.sixDimResidualMatrixA hq (by simp) -
        S.sixDimResidualMatrixB hq (by simp)) *
      (S.sixDimResidualMatrixA hq (by simp) -
        S.sixDimResidualMatrixB hq (by simp)) = 1) :
    (S.residualA - S.residualB) *
      (S.residualA - S.residualB) = 1 := by
  let T : TwoH →L[ℂ] TwoH :=
    S.sixDimEuclideanResidualA hq (by simp) -
      S.sixDimEuclideanResidualB hq (by simp)
  have hmatrix :
      twoEuclideanCstarMatrix T =
        S.sixDimResidualMatrixA hq (by simp) -
          S.sixDimResidualMatrixB hq (by simp) := by
    change twoEuclideanCstarMatrix
        (S.sixDimEuclideanResidualA hq (by simp) -
          S.sixDimEuclideanResidualB hq (by simp)) = _
    rw [twoEuclideanCstarMatrix_sub]
    exact congrArg₂ (· - ·)
      (S.sixDimCstarResidualMatrixA_eq hq (by simp))
      (S.sixDimCstarResidualMatrixB_eq hq (by simp))
  have heuc : T * T = 1 := by
    apply twoEuclideanCstarMatrix_involution_lift
    rw [hmatrix]
    exact hmat
  let U := (S.sixDimResidualBasis hq (by simp)).repr
  have hconj : hilbertIsometricConjugate U
        (S.residualA - S.residualB) = T := by
    rw [hilbertIsometricConjugate_sub]
    rfl
  apply hilbertIsometricConjugate_involution_lift U
  rw [hconj]
  exact heuc

end Neoplatonic.LTR
