import Neoplatonic.LTR.SixDimensionalCornerSpectralRank
import Neoplatonic.LTR.SixDimensionalSignedWitnessTraceEnergy
import Mathlib.Tactic

/-!
# LTR-MAN-94: the true saturated Hamming corner has complex rank two

MAN-92 proves that each surviving signed-witness neutral truth
sector has exactly two Hilbert coordinates. Its actual diagonal
0/1 truth-sector projector Q therefore has trace two.

MAN-94's four block equations and MAN-93's corner tripotence
imply that the full corner compression X=(I-Q)W(I-Q)
has rank equal to that of its idempotent square. The trace
identity fixes both ranks at two.

This formalizes the true six-dimensional rank constraint for
both signs of the exact-Hamming saturation, including the
opposite-double 2+2 corner multiplicity configurations.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The trace of an actual diagonal truth-sector projector is
the cardinality of its six-coordinate labelled fibre subset. -/
theorem sixTruthSectorProjection_trace_eq_card
    (label : Fin 6 → Fin 4)
    (sector : Fin 4 → Prop) [DecidablePred sector] :
    (sixTruthSectorProjection label sector).trace =
      ((Finset.univ.filter (fun i : Fin 6 =>
        sector (label i))).card : ℂ) := by
  classical
  change (Matrix.diagonal (fun i : Fin 6 =>
    if sector (label i) then (1 : ℂ) else 0)).trace = _
  rw [Matrix.trace_diagonal]
  simp [Finset.sum_ite, Finset.sum_const, nsmul_eq_mul]

/-- Under 00↔11 saturated exact Hamming distances, the true
corner compression of the plus signed Dirac witness and its
idempotent square both have rank exactly two. -/
theorem sixLabelled_exactHamming_saturated03_cornerRankTwo
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    (sixComplementCornerBlock W Q).rank = 2 ∧
      ((sixComplementCornerBlock W Q) *
        (sixComplementCornerBlock W Q)).rank = 2 := by
  dsimp only
  have hW := sixLabelled_exactHamming_saturated03_trueMatrixPlus_involution
    label D hD hham h03 h12
  have hQtr :
      (sixTruthSectorProjection label squarePlusNeutral).trace =
        (2 : ℂ) := by
    rw [sixTruthSectorProjection_trace_eq_card,
      sixPlusNeutral_card_eq_fibreSum,
      sixLabelled_plusWitness_saturated_neutral_fibreSum_two
        label D hD hW h03]
    norm_num
  apply sixMatrix_involution_neutralTraceTwo_cornerRankTwo
  · exact hW
  · exact sixTruthSectorProjection_idempotent label squarePlusNeutral
  · exact sixTruthSectorProjection_W_zero
      label squarePlusNeutral _
      (sixLabelled_plusWitness_neutral_entry_zero label D)
  · exact hQtr

/-- The true 01↔10 saturated difference witness has
rank-two corner compression, with rank-two idempotent square. -/
theorem sixLabelled_exactHamming_saturated12_cornerRankTwo
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = 0)
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    let W := labelledSquareA label D - labelledSquareB label D
    let Q := sixTruthSectorProjection label squareMinusNeutral
    (sixComplementCornerBlock W Q).rank = 2 ∧
      ((sixComplementCornerBlock W Q) *
        (sixComplementCornerBlock W Q)).rank = 2 := by
  dsimp only
  have hW := sixLabelled_exactHamming_saturated12_trueMatrixMinus_involution
    label D hD hham h03 h12
  have hQtr :
      (sixTruthSectorProjection label squareMinusNeutral).trace =
        (2 : ℂ) := by
    rw [sixTruthSectorProjection_trace_eq_card,
      sixMinusNeutral_card_eq_fibreSum,
      sixLabelled_minusWitness_saturated_neutral_fibreSum_two
        label D hD hW h12]
    norm_num
  apply sixMatrix_involution_neutralTraceTwo_cornerRankTwo
  · exact hW
  · exact sixTruthSectorProjection_idempotent label squareMinusNeutral
  · exact sixTruthSectorProjection_W_zero
      label squareMinusNeutral _
      (sixLabelled_minusWitness_neutral_entry_zero label D)
  · exact hQtr

end Neoplatonic.LTR
