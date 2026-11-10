import Neoplatonic.LTR.ResidualIsometricConjugation
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-69: genuine matrix C*-norm bounds for the 6D residual

MAN-68 transports the compressed residual coordinate operators into
two-dimensional complex Euclidean Hilbert space by a common isometry.

Mathlib's matrix-to-continuous-operator star algebra equivalence is
isometric for the genuine L2 operator norm. We use its inverse to form
two-by-two matrices with exact inherited plus/minus contraction bounds.

The remaining step for the Pauli coefficient bounds is to identify
these matrices' traces with the zero traces established in MAN-64.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev TwoEuclidean := EuclideanSpace ℂ (Fin 2)
private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- The concrete matrix of a bounded operator on the standard
two-dimensional complex Euclidean Hilbert space. -/
noncomputable def twoEuclideanCstarMatrix
    (T : TwoEuclidean →L[ℂ] TwoEuclidean) : TwoMat :=
  (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).symm T

/-- The natural matrix-to-operator star algebra equivalence
preserves the actual Hilbert operator norm exactly. -/
theorem twoEuclideanCstarMatrix_norm
    (T : TwoEuclidean →L[ℂ] TwoEuclidean) :
    ‖twoEuclideanCstarMatrix T‖ = ‖T‖ := by
  have h := StarAlgEquiv.norm_map
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ))
    (twoEuclideanCstarMatrix T)
  simpa [twoEuclideanCstarMatrix] using h.symm

theorem twoEuclideanCstarMatrix_add
    (T S : TwoEuclidean →L[ℂ] TwoEuclidean) :
    twoEuclideanCstarMatrix (T + S) =
      twoEuclideanCstarMatrix T + twoEuclideanCstarMatrix S := by
  unfold twoEuclideanCstarMatrix
  exact map_add (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).symm T S

theorem twoEuclideanCstarMatrix_sub
    (T S : TwoEuclidean →L[ℂ] TwoEuclidean) :
    twoEuclideanCstarMatrix (T - S) =
      twoEuclideanCstarMatrix T - twoEuclideanCstarMatrix S := by
  unfold twoEuclideanCstarMatrix
  exact map_sub (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).symm T S

theorem twoEuclideanCstarMatrix_simultaneous_norm
    (T S : TwoEuclidean →L[ℂ] TwoEuclidean) :
    ‖twoEuclideanCstarMatrix T + twoEuclideanCstarMatrix S‖ =
      ‖T + S‖ ∧
    ‖twoEuclideanCstarMatrix T - twoEuclideanCstarMatrix S‖ =
      ‖T - S‖ := by
  constructor
  · rw [← twoEuclideanCstarMatrix_add,
      twoEuclideanCstarMatrix_norm]
  · rw [← twoEuclideanCstarMatrix_sub,
      twoEuclideanCstarMatrix_norm]

section ConcreteSixDimensionalResidual

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]

/-- Concrete Hilbert-operator matrix associated with the
actual compressed coordinate A. -/
noncomputable def TwoDirectionExtremalSystem.sixDimCstarResidualMatrixA
    (S : TwoDirectionExtremalSystem H)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ H = 6) : TwoMat :=
  twoEuclideanCstarMatrix (S.sixDimEuclideanResidualA hq hDim)

/-- Coordinate B transported into the same concrete 2×2 matrix
algebra and the same residual Hilbert basis. -/
noncomputable def TwoDirectionExtremalSystem.sixDimCstarResidualMatrixB
    (S : TwoDirectionExtremalSystem H)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ H = 6) : TwoMat :=
  twoEuclideanCstarMatrix (S.sixDimEuclideanResidualB hq hDim)

/-- The original pairwise Hamming contractions now hold
for the true complex 2×2 matrices in the C*-operator norm. -/
theorem TwoDirectionExtremalSystem.sixDimCstarResidual_contracts
    (S : TwoDirectionExtremalSystem H)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ H = 6) :
    ‖S.sixDimCstarResidualMatrixA hq hDim +
       S.sixDimCstarResidualMatrixB hq hDim‖ ≤ 1 ∧
    ‖S.sixDimCstarResidualMatrixA hq hDim -
       S.sixDimCstarResidualMatrixB hq hDim‖ ≤ 1 := by
  have h := twoEuclideanCstarMatrix_simultaneous_norm
    (S.sixDimEuclideanResidualA hq hDim)
    (S.sixDimEuclideanResidualB hq hDim)
  have hbase := S.sixDimEuclideanResidual_contracts hq hDim
  exact ⟨h.1.trans_le hbase.1, h.2.trans_le hbase.2⟩

end ConcreteSixDimensionalResidual
end Neoplatonic.LTR
