import Neoplatonic.LTR.SixDimensionalActualMinusResidualRankZero
import Neoplatonic.LTR.TwoDimensionalRealPauliVectors
import Neoplatonic.LTR.SixDimensionalPauliOppositeEnergyRegions
import Mathlib.Tactic

/-!
# LTR-MAN-181: overneutral signed rank fixes the *sign* of Pauli overlap

MAN-178 proves the true residual negative-witness scalar zero
whenever the original 01/10 truth fibres are singleton:
  muMinus = q+r-c = 0.

First-bit truth translation carries the original negative witness
to the translated positive witness and the original Pauli
imbalance c to -c.

The translated residual 2x2 matrices are Hermitian, so their
real Pauli squared lengths q and r are nonnegative. Therefore

  c_original = q_translated + r_translated >= 0.

MAN-84 identifies c_original with 2(E03-E12) in the actual
original Hermitian six-dimensional Dirac matrix. Consequently
  E03 >= E12
holds throughout the *entire* interior region of the two-bit
Hamming Connes metric for the original m01=m10=1 stratum.
No saturation, near-half approximation, or additional hypotheses.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ
private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- The actual oriented original Pauli imbalance equals the
sum of nonnegative real squared lengths of the *translated*
Hermitian two-dimensional residual matrices. -/
theorem sixLabelled_exactHamming_overneutral_pauliImbalance_eq_residualSquares
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
      sixOrientedOppositeEnergyImbalance label D =
        pauliRealQuadratic (S.sixDimResidualMatrixA hq (by simp)) +
          pauliRealQuadratic (S.sixDimResidualMatrixB hq (by simp)) := by
  dsimp only
  let tau := twoBitSquareTranslation 1
  obtain ⟨S, hq, hA, hB, hMu⟩ :=
    sixLabelled_exactHamming_overneutral_minusResidualPauli_zero
      label D hD hham hm1 hm2
  let M : TwoMat := S.sixDimResidualMatrixA hq (by simp)
  let N : TwoMat := S.sixDimResidualMatrixB hq (by simp)
  have hReal :
      pauliRealQuadratic M + pauliRealQuadratic N +
        pauliRealMixed M N = 0 := by
    have h := congrArg Complex.re hMu
    simpa [pauliRealQuadratic, pauliRealMixed] using h
  have hBridge :
      pauliMixed M N =
        ((sixOrientedOppositeEnergyImbalance (tau ∘ label) D : ℝ) : ℂ) :=
    sixLabelled_extremal_pauliMixed_eq_realImbalance
      (tau ∘ label) D hD S hq hA hB
  have hMix :
      pauliRealMixed M N =
        -sixOrientedOppositeEnergyImbalance label D := by
    change (pauliMixed M N).re = _
    rw [hBridge, sixOrientedOppositeEnergyImbalance_translationOne_neg]
    simp
  refine ⟨S, hq, hA, hB, ?_⟩
  change sixOrientedOppositeEnergyImbalance label D =
    pauliRealQuadratic M + pauliRealQuadratic N
  linarith

/-- The original signed Pauli overlap is nonnegative whenever
both 01 and 10 truth fibres are singleton, over the full
non-saturated exact-Hamming region. -/
theorem sixLabelled_exactHamming_overneutral_pauliImbalance_nonneg
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1) :
    0 ≤ sixOrientedOppositeEnergyImbalance label D := by
  obtain ⟨S, hq, _, _, hEq⟩ :=
    sixLabelled_exactHamming_overneutral_pauliImbalance_eq_residualSquares
      label D hD hham hm1 hm2
  let M : TwoMat := S.sixDimResidualMatrixA hq (by simp)
  let N : TwoMat := S.sixDimResidualMatrixB hq (by simp)
  have hM : M.IsHermitian :=
    S.sixDimResidualMatrixA_isHermitian hq (by simp)
  have hN : N.IsHermitian :=
    S.sixDimResidualMatrixB_isHermitian hq (by simp)
  have hq0 := pauliRealQuadratic_nonneg M hM
  have hr0 := pauliRealQuadratic_nonneg N hN
  change sixOrientedOppositeEnergyImbalance label D =
    pauliRealQuadratic M + pauliRealQuadratic N at hEq
  rw [hEq]
  exact add_nonneg hq0 hr0

/-- This signed-overlap positivity is a direct, basis-free
inequality between the original opposite truth-fibre squared
Dirac coupling energies. -/
theorem sixLabelled_exactHamming_overneutral_oppositeEnergy_order
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1) :
    sixTruthFibreBlockEnergy label D 1 2 ≤
      sixTruthFibreBlockEnergy label D 0 3 := by
  have h := sixLabelled_exactHamming_overneutral_pauliImbalance_nonneg
    label D hD hham hm1 hm2
  change (0 : ℝ) ≤ 2 *
    (sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2) at h
  linarith

end Neoplatonic.LTR
