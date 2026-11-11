import Neoplatonic.LTR.SixDimensionalSignedOppositeRankOne
import Neoplatonic.LTR.SixDimensionalSignedOppositeRankOneMinus
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# LTR-MAN-95: vanishing minors of saturated six-dimensional opposite Dirac blocks

The actual labelled 00 -> 11 and 01 -> 10 Dirac blocks have
rank one at the corresponding exact-Hamming saturation.
Every two-by-two minor therefore vanishes, including the
opposite-double truth-fibre case, in the original Hilbert chart.

This result makes no choice of a 2x2 coordinate permutation.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Every two-by-two minor of a complex six-dimensional rank-one
matrix is zero, even when rows or columns repeat. -/
theorem sixMatrix_rankOne_allTwoByTwoMinors_zero
    (B : SixMat) (hRank : B.rank = 1)
    (i k j l : Fin 6) :
    B i j * B k l = B i l * B k j := by
  let r : Fin 2 → Fin 6 := fun t => if t = 0 then i else k
  let c : Fin 2 → Fin 6 := fun t => if t = 0 then j else l
  let M : Matrix (Fin 2) (Fin 2) ℂ := B.submatrix r c
  have hSmall : M.rank ≤ 1 := by
    exact (Matrix.rank_submatrix_le B r c).trans_eq hRank
  have hDet : M.det = 0 := by
    by_contra hNonzero
    have hFull : M.rank = 2 := by
      simpa only [Fintype.card_fin] using
        (Matrix.rank_of_det_ne_zero hNonzero)
    omega
  have hEntries : B i j * B k l - B i l * B k j = 0 := by
    simpa [M, r, c, Matrix.det_fin_two] using hDet
  exact sub_eq_zero.mp hEntries

/-- Positive saturation forces every 2x2 minor of the original
00-to-11 Dirac block to vanish, including the 2+2 case. -/
theorem sixLabelled_exactHamming_saturated03_oppositeBlock_allMinors_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (i k j l : Fin 6) :
    sixTruthFibreBlock label D 0 3 i j *
        sixTruthFibreBlock label D 0 3 k l =
      sixTruthFibreBlock label D 0 3 i l *
        sixTruthFibreBlock label D 0 3 k j := by
  apply sixMatrix_rankOne_allTwoByTwoMinors_zero
  exact sixLabelled_exactHamming_saturated03_oppositeBlockRankOne
    label D hD hham h03 h12

/-- Negative saturation gives the same minor certificate for
the original 01-to-10 Dirac block. -/
theorem sixLabelled_exactHamming_saturated12_oppositeBlock_allMinors_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = 0)
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ))
    (i k j l : Fin 6) :
    sixTruthFibreBlock label D 1 2 i j *
        sixTruthFibreBlock label D 1 2 k l =
      sixTruthFibreBlock label D 1 2 i l *
        sixTruthFibreBlock label D 1 2 k j := by
  apply sixMatrix_rankOne_allTwoByTwoMinors_zero
  exact sixLabelled_exactHamming_saturated12_oppositeBlockRankOne
    label D hD hham h03 h12

end Neoplatonic.LTR
