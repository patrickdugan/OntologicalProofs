import Neoplatonic.LTR.SixDimensionalCornerComplementaryProjections
import Neoplatonic.LTR.SixDimensionalSignedCornerRankTwo
import Mathlib.Tactic

/-!
# LTR-MAN-97: genuine saturated signed Hamming witness spectral splitting

MAN-97's complementary rank-two corner projections apply directly to
the six-dimensional labelled Dirac witnesses proven involutive in MAN-91.
Both signs have a neutral truth sector of trace two, and MAN-94
identifies the actual Hermitian neutral/corner exchange maps.

For W = i[D,P+Q] with 00/11 saturation or W = i[D,P-Q]
with 01/10 saturation, the corner compression X and the
neutral-to-corner map Y satisfy

  X² + YYᴴ = C,    X² YYᴴ = YYᴴ X² = 0,

where X² and YYᴴ are orthogonal rank-two projections in
the complete six-dimensional coordinate representation.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Positive saturation yields the complementary two-plane
corner projections of the original signed Dirac witness. -/
theorem sixLabelled_exactHamming_saturated03_cornerOrthogonalSplit
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    let X := C * W * C
    let Y := C * W * Q
    (X * X) * (X * X) = X * X ∧
      (Y * Y.conjTranspose) * (Y * Y.conjTranspose) =
        Y * Y.conjTranspose ∧
      (X * X) * (Y * Y.conjTranspose) = 0 ∧
      (Y * Y.conjTranspose) * (X * X) = 0 ∧
      X * X + Y * Y.conjTranspose = C ∧
      (X * X).rank = 2 ∧
      (Y * Y.conjTranspose).rank = 2 := by
  dsimp only
  have hW :=
    sixLabelled_exactHamming_saturated03_trueMatrixPlus_involution
      label D hD hham h03 h12
  have hQtr :
      (sixTruthSectorProjection label squarePlusNeutral).trace =
        (2 : ℂ) := by
    rw [sixTruthSectorProjection_trace_eq_card,
      sixPlusNeutral_card_eq_fibreSum,
      sixLabelled_plusWitness_saturated_neutral_fibreSum_two
        label D hD hW h03]
    norm_num
  apply sixMatrix_hermitianInvolution_zeroNeutral_orthogonalCornerSplit
  · exact hW
  · exact sixLabelled_plusWitness_isHermitian label D hD
  · exact sixTruthSectorProjection_idempotent label squarePlusNeutral
  · exact sixTruthSectorProjection_W_zero
      label squarePlusNeutral _
      (sixLabelled_plusWitness_neutral_entry_zero label D)
  · exact sixTruthSectorProjection_isHermitian label squarePlusNeutral
  · exact hQtr

/-- Negative saturation gives the same orthogonal rank-two
corner splitting in the genuine 01/10 opposite-block witness. -/
theorem sixLabelled_exactHamming_saturated12_cornerOrthogonalSplit
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = 0)
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    let W := labelledSquareA label D - labelledSquareB label D
    let Q := sixTruthSectorProjection label squareMinusNeutral
    let C := (1 - Q : SixMat)
    let X := C * W * C
    let Y := C * W * Q
    (X * X) * (X * X) = X * X ∧
      (Y * Y.conjTranspose) * (Y * Y.conjTranspose) =
        Y * Y.conjTranspose ∧
      (X * X) * (Y * Y.conjTranspose) = 0 ∧
      (Y * Y.conjTranspose) * (X * X) = 0 ∧
      X * X + Y * Y.conjTranspose = C ∧
      (X * X).rank = 2 ∧
      (Y * Y.conjTranspose).rank = 2 := by
  dsimp only
  have hW :=
    sixLabelled_exactHamming_saturated12_trueMatrixMinus_involution
      label D hD hham h03 h12
  have hQtr :
      (sixTruthSectorProjection label squareMinusNeutral).trace =
        (2 : ℂ) := by
    rw [sixTruthSectorProjection_trace_eq_card,
      sixMinusNeutral_card_eq_fibreSum,
      sixLabelled_minusWitness_saturated_neutral_fibreSum_two
        label D hD hW h12]
    norm_num
  apply sixMatrix_hermitianInvolution_zeroNeutral_orthogonalCornerSplit
  · exact hW
  · exact sixLabelled_minusWitness_isHermitian label D hD
  · exact sixTruthSectorProjection_idempotent label squareMinusNeutral
  · exact sixTruthSectorProjection_W_zero
      label squareMinusNeutral _
      (sixLabelled_minusWitness_neutral_entry_zero label D)
  · exact sixTruthSectorProjection_isHermitian label squareMinusNeutral
  · exact hQtr

end Neoplatonic.LTR
