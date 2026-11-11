import Neoplatonic.LTR.SixDimensionalHilbertResidualInvolution
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-145: transport the exact Pauli scalar square to the true residual

MAN-90 already transports a square-one two-by-two Pauli identity
into the genuine residual Hilbert operator. This module extends
that result to an arbitrary complex scalar coefficient mu:

  (M_A+M_B)² = mu I₂
      => (R_A+R_B)² = mu I_res.

The proof passes through the original common residual isometric
basis, Euclidean C*-matrix equivalence, and the injective
conjugation. Every operation is on the original genuine compressed
six-dimensional Dirac coordinate operators.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev TwoH := EuclideanSpace ℂ (Fin 2)
private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- The canonical complex 2x2 C*-matrix isomorphism transports an
arbitrary scalar square back to Euclidean bounded operators. -/
theorem twoEuclideanCstarMatrix_scalarSquare_lift
    (T : TwoH →L[ℂ] TwoH) (mu : ℂ)
    (h : twoEuclideanCstarMatrix T *
      twoEuclideanCstarMatrix T = mu • (1 : TwoMat)) :
    T * T = mu • (1 : TwoH →L[ℂ] TwoH) := by
  let F := (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).symm
  have h' : F (T * T) = mu • (1 : TwoMat) := by
    simpa only [twoEuclideanCstarMatrix, map_mul] using h
  apply F.injective
  simpa only [map_smul, map_one] using h'

/-- Isometric Hilbert conjugation reflects scalar-square
identities for arbitrary complex mu, on the genuine residual. -/
theorem hilbertIsometricConjugate_scalarSquare_lift
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (U : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) (mu : ℂ)
    (h : hilbertIsometricConjugate U T *
      hilbertIsometricConjugate U T =
        mu • (1 : F →L[ℂ] F)) :
    T * T = mu • (1 : E →L[ℂ] E) := by
  apply ContinuousLinearMap.ext
  intro x
  have hx := congrArg
    (fun R : F →L[ℂ] F => R (U x)) h
  have hx' : U (T (T x)) = mu • U x := by
    simpa [hilbertIsometricConjugate] using hx
  change T (T x) = mu • x
  apply U.injective
  simpa only [map_smul] using hx'

/-- The exact scalar Pauli square of the original 2x2 residual
matrices transports to the true residual Hilbert coordinate sum. -/
theorem TwoDirectionExtremalSystem.residualPlus_scalarSquare_of_pauli
    (S : TwoDirectionExtremalSystem SixH)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (mu : ℂ)
    (hmat :
      (S.sixDimResidualMatrixA hq (by simp) +
        S.sixDimResidualMatrixB hq (by simp)) *
      (S.sixDimResidualMatrixA hq (by simp) +
        S.sixDimResidualMatrixB hq (by simp)) =
        mu • (1 : TwoMat)) :
    (S.residualA + S.residualB) *
      (S.residualA + S.residualB) =
      mu • (1 : S.residual →L[ℂ] S.residual) := by
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
  have heuc : T * T = mu • (1 : TwoH →L[ℂ] TwoH) := by
    apply twoEuclideanCstarMatrix_scalarSquare_lift
    rw [hmatrix]
    exact hmat
  let U := (S.sixDimResidualBasis hq (by simp)).repr
  have hconj : hilbertIsometricConjugate U
        (S.residualA + S.residualB) = T := by
    rw [hilbertIsometricConjugate_add]
    rfl
  apply hilbertIsometricConjugate_scalarSquare_lift U
  rw [hconj]
  exact heuc

end Neoplatonic.LTR
