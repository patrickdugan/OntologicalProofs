import Neoplatonic.LTR.SixDimensionalOverneutralPauliSign
import Neoplatonic.LTR.SixDimensionalNegativeNearHalfDefect
import Neoplatonic.LTR.TwoDimensionalRealPauliVectors
import Mathlib.Tactic

/-!
# LTR-MAN-183: the overneutral original Pauli Gram matrix is saturated in the interior

MAN-181 proves that the original oriented Pauli mixed coefficient c
equals q'+r', the sum of translated Hermitian residual squared lengths,
whenever the true 01 and 10 truth fibres are singleton.

MAN-72 supplies the exact Gram determinant condition c²≤4q'r'.
The elementary identity
  (q'+r')² - 4q'r' = (q'-r')²
then forces q'=r' and c=2q'=2r'. Thus the residual Gram determinant
vanishes *throughout the interior*, not just near the forbidden
maximal Pauli overlap.

The true original Dirac opposite-fibre energy difference also equals
the common translated residual Pauli squared length:
  E03-E12 = q'=r'.

This holds in the same six-dimensional Hermitian Dirac chart with
no additional spectral-saturation or truth-gauge assumptions.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ
private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- The boundary q+r=c of a real positive semidefinite two-vector
Gram cone forces equality of both squared lengths and exact
saturation of the Cauchy determinant. -/
theorem realGram_sum_eq_mixed_forces_equal_lengths
    (q r c : ℝ)
    (hDet : c ^ 2 ≤ 4 * q * r)
    (hSum : c = q + r) :
    q = r ∧ c = 2 * q := by
  have hDiff : (q - r) ^ 2 ≤ 0 := by
    nlinarith [hDet]
  have hqr : q = r := by
    nlinarith [sq_nonneg (q - r)]
  exact ⟨hqr, by linarith⟩

/-- Under exact Hamming and singleton neutral truth fibres, the
two actual translated Pauli residual squared lengths coincide.
The original Dirac Pauli imbalance is twice either one. -/
theorem sixLabelled_exactHamming_overneutral_residualPauli_lengths_equal
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1) :
    let tau := twoBitSquareTranslation 1
    ∃ S : TwoDirectionExtremalSystem SixH,
      ∃ hq : Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus),
      S.A = sixLabelledAOperator (tau ∘ label) D ∧
      S.B = sixLabelledBOperator (tau ∘ label) D ∧
      pauliRealQuadratic (S.sixDimResidualMatrixA hq (by simp)) =
        pauliRealQuadratic (S.sixDimResidualMatrixB hq (by simp)) ∧
      sixOrientedOppositeEnergyImbalance label D =
        2 * pauliRealQuadratic (S.sixDimResidualMatrixA hq (by simp)) := by
  dsimp only
  let tau := twoBitSquareTranslation 1
  obtain ⟨S, hq, hA, hB, hSum⟩ :=
    sixLabelled_exactHamming_overneutral_pauliImbalance_eq_residualSquares
      label D hD hham hm1 hm2
  let M : TwoMat := S.sixDimResidualMatrixA hq (by simp)
  let N : TwoMat := S.sixDimResidualMatrixB hq (by simp)
  let q : ℝ := pauliRealQuadratic M
  let rr : ℝ := pauliRealQuadratic N
  let c : ℝ := sixOrientedOppositeEnergyImbalance label D
  change c = q + rr at hSum
  have hM : M.IsHermitian :=
    S.sixDimResidualMatrixA_isHermitian hq (by simp)
  have hN : N.IsHermitian :=
    S.sixDimResidualMatrixB_isHermitian hq (by simp)
  have hMixedBridge :
      pauliMixed M N =
        ((sixOrientedOppositeEnergyImbalance (tau ∘ label) D : ℝ) : ℂ) :=
    sixLabelled_extremal_pauliMixed_eq_realImbalance
      (tau ∘ label) D hD S hq hA hB
  have hMixed : pauliRealMixed M N = -c := by
    change (pauliMixed M N).re = -c
    rw [hMixedBridge, sixOrientedOppositeEnergyImbalance_translationOne_neg]
    simp
  have hGram := twoDim_pauli_realGram_psd M N hM hN
  change (pauliRealMixed M N) ^ 2 ≤ 4 * q * rr at hGram
  have hDet : c ^ 2 ≤ 4 * q * rr := by
    rw [hMixed] at hGram
    nlinarith
  obtain ⟨hqr, hcEq⟩ :=
    realGram_sum_eq_mixed_forces_equal_lengths q rr c hDet hSum
  refine ⟨S, hq, hA, hB, ?_, ?_⟩
  · exact hqr
  · exact hcEq

/-- The original 00/11-minus-01/10 directed energy difference
equals the translated residual Pauli squared length. -/
theorem sixLabelled_exactHamming_overneutral_energyDiff_eq_residualPauliLength
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1) :
    let tau := twoBitSquareTranslation 1
    ∃ S : TwoDirectionExtremalSystem SixH,
      ∃ hq : Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus),
      S.A = sixLabelledAOperator (tau ∘ label) D ∧
      S.B = sixLabelledBOperator (tau ∘ label) D ∧
      pauliRealQuadratic (S.sixDimResidualMatrixA hq (by simp)) =
        pauliRealQuadratic (S.sixDimResidualMatrixB hq (by simp)) ∧
      sixTruthFibreBlockEnergy label D 0 3 -
        sixTruthFibreBlockEnergy label D 1 2 =
          pauliRealQuadratic (S.sixDimResidualMatrixA hq (by simp)) := by
  dsimp only
  obtain ⟨S, hq, hA, hB, hqr, hc⟩ :=
    sixLabelled_exactHamming_overneutral_residualPauli_lengths_equal
      label D hD hham hm1 hm2
  refine ⟨S, hq, hA, hB, hqr, ?_⟩
  change 2 * (sixTruthFibreBlockEnergy label D 0 3 -
    sixTruthFibreBlockEnergy label D 1 2) =
      2 * pauliRealQuadratic (S.sixDimResidualMatrixA hq (by simp)) at hc
  linarith

end Neoplatonic.LTR
