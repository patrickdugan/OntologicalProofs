import Neoplatonic.LTR.SixDimensionalActualResidualRankPauliZero
import Neoplatonic.LTR.SixDimensionalSignedBitFlipTransport
import Neoplatonic.LTR.SixDimensionalOverneutralSignedRank
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# LTR-MAN-178: the true overneutral negative signed Pauli residual is zero

MAN-174 certifies that whenever the true 01 and 10 truth
fibres are singleton, the original negative signed Hamming
witness Wminus=A−B has matrix rank at most 4.

First-bit truth translation preserves every Hamming distance,
negates A and retains B, and therefore carries the positive
signed witness to -Wminus in the original matrix coordinates.
Matrix rank is unchanged by multiplication by the nonzero
complex scalar -1.

Applying MAN-177 to that translated positive witness gives the
zero residual Pauli scalar identity in the actual translated
common Hermitian residual basis. Since the translated positive
witness is -Wminus, this certifies full residual annihilation
for the original negative sign without an energy saturation
premise or an interior-overlap restriction.

This opens a direct algebraic route to suppressing the original
opposite neutral 01/10 Dirac energy in these fibre patterns.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The ordinary algebraic matrix rank is unchanged under sign
negation in the original six-dimensional complex coordinates. -/
theorem sixMatrix_rank_neg_eq (W : SixMat) :
    (-W).rank = W.rank := by
  have hNZ : (-1 : ℂ) ∈ nonZeroDivisors ℂ :=
    mem_nonZeroDivisors_of_ne_zero (by norm_num)
  have h := Matrix.rank_smul_of_mem_nonZeroDivisors W hNZ
  simpa only [neg_one_smul] using h

/-- The original negative signed witness rank bound transports
to the translated positive signed Hamming witness. -/
theorem sixLabelled_minusNeutralSingletons_translatedPlus_rank_le_four
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1) :
    (labelledSquareA (twoBitSquareTranslation 1 ∘ label) D +
      labelledSquareB (twoBitSquareTranslation 1 ∘ label) D).rank ≤ 4 := by
  have hnegRank :=
    sixLabelled_minusWitness_rank_le_four_of_neutralSingletons
      label D hm1 hm2
  rw [sixLabelled_plusWitness_translationOne_eq_negMinus]
  rw [sixMatrix_rank_neg_eq]
  exact hnegRank

/-- For exact-Hamming original six-dimensional Hermitian Dirac
matrices with singleton 01/10 truth fibres, the translated
actual residual Pauli SUM scalar vanishes. This is the original
negative-witness scalar square, since Wplus'=-Wminus. -/
theorem sixLabelled_exactHamming_overneutral_minusResidualPauli_zero
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
      pauliQuadratic (S.sixDimResidualMatrixA hq (by simp)) +
        pauliQuadratic (S.sixDimResidualMatrixB hq (by simp)) +
        pauliMixed (S.sixDimResidualMatrixA hq (by simp))
          (S.sixDimResidualMatrixB hq (by simp)) = 0 := by
  dsimp only
  let tau := twoBitSquareTranslation 1
  have hham' :
      ∀ u v : Fin 4,
        sixLabelledConnesDistance (tau ∘ label) D u v =
          (twoBitSquareHamming u v : ℝ≥0∞) :=
    sixLabelled_exactHamming_truthTranslation label D 1 hham
  have hRank' :=
    sixLabelled_minusNeutralSingletons_translatedPlus_rank_le_four
      label D hm1 hm2
  exact sixLabelled_exactHamming_plusRankLeFour_pauliScalar_zero
    (tau ∘ label) D hD hham' hRank'

end Neoplatonic.LTR
