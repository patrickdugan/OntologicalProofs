import Neoplatonic.LTR.TwoDimensionalPauliOperatorNorm
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Tactic

/-!
# LTR-MAN-68: isometric Hilbert-basis conjugation of residual operators

The MAN-60 residual coordinate operators act on an invariant
Hilbert subspace. The orthonormal basis constructed in MAN-65
gives a linear isometry to standard complex Euclidean space.
The operators and their simultaneous contractions transport
isometrically to those coordinates.

Identifying these transported continuous operators with the
explicit matrices of MAN-65 is the next formal step.
-/

namespace Neoplatonic.LTR

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Conjugation of a bounded operator by a linear isometry. -/
noncomputable def hilbertIsometricConjugate
    (U : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) : F →L[ℂ] F :=
  (U : E →L[ℂ] F).comp (T.comp (U.symm : F →L[ℂ] E))

/-- An isometric basis change preserves the operator norm exactly. -/
theorem hilbertIsometricConjugate_norm
    (U : E ≃ₗᵢ[ℂ] F) (T : E →L[ℂ] E) :
    ‖hilbertIsometricConjugate U T‖ = ‖T‖ := by
  unfold hilbertIsometricConjugate
  rw [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

/-- The isometric conjugate of an operator sum is the sum of conjugates. -/
theorem hilbertIsometricConjugate_add
    (U : E ≃ₗᵢ[ℂ] F) (A B : E →L[ℂ] E) :
    hilbertIsometricConjugate U (A + B) =
      hilbertIsometricConjugate U A +
        hilbertIsometricConjugate U B := by
  ext x
  simp [hilbertIsometricConjugate]

/-- Isometric conjugation also preserves subtraction. -/
theorem hilbertIsometricConjugate_sub
    (U : E ≃ₗᵢ[ℂ] F) (A B : E →L[ℂ] E) :
    hilbertIsometricConjugate U (A - B) =
      hilbertIsometricConjugate U A -
        hilbertIsometricConjugate U B := by
  ext x
  simp [hilbertIsometricConjugate]

/-- Both simultaneous contraction norms are unchanged by the
same isometric change of Hilbert coordinates. -/
theorem hilbertIsometricConjugate_simultaneous_norm
    (U : E ≃ₗᵢ[ℂ] F) (A B : E →L[ℂ] E) :
    ‖hilbertIsometricConjugate U A +
        hilbertIsometricConjugate U B‖ = ‖A + B‖ ∧
    ‖hilbertIsometricConjugate U A -
        hilbertIsometricConjugate U B‖ = ‖A - B‖ := by
  constructor
  · rw [← hilbertIsometricConjugate_add,
      hilbertIsometricConjugate_norm]
  · rw [← hilbertIsometricConjugate_sub,
      hilbertIsometricConjugate_norm]

section ActualSixDimensionalResidual

variable {H : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H] [CompleteSpace H]

/-- The compressed coordinate A transported to Euclidean coordinates. -/
noncomputable def TwoDirectionExtremalSystem.sixDimEuclideanResidualA
    (S : TwoDirectionExtremalSystem H)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ H = 6) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  hilbertIsometricConjugate
    (S.sixDimResidualBasis hq hDim).repr S.residualA

/-- The compressed coordinate B in the same Euclidean basis. -/
noncomputable def TwoDirectionExtremalSystem.sixDimEuclideanResidualB
    (S : TwoDirectionExtremalSystem H)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ H = 6) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  hilbertIsometricConjugate
    (S.sixDimResidualBasis hq hDim).repr S.residualB

/-- The true plus and minus contractions hold in the standard
two-dimensional Euclidean coordinate representation. -/
theorem TwoDirectionExtremalSystem.sixDimEuclideanResidual_contracts
    (S : TwoDirectionExtremalSystem H)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ H = 6) :
    ‖S.sixDimEuclideanResidualA hq hDim +
       S.sixDimEuclideanResidualB hq hDim‖ ≤ 1 ∧
    ‖S.sixDimEuclideanResidualA hq hDim -
       S.sixDimEuclideanResidualB hq hDim‖ ≤ 1 := by
  let U := (S.sixDimResidualBasis hq hDim).repr
  have h := hilbertIsometricConjugate_simultaneous_norm
    U S.residualA S.residualB
  change ‖hilbertIsometricConjugate U S.residualA +
       hilbertIsometricConjugate U S.residualB‖ ≤ 1 ∧
    ‖hilbertIsometricConjugate U S.residualA -
       hilbertIsometricConjugate U S.residualB‖ ≤ 1
  exact ⟨h.1.trans_le S.residual_plus_le,
    h.2.trans_le S.residual_minus_le⟩

end ActualSixDimensionalResidual
end Neoplatonic.LTR
