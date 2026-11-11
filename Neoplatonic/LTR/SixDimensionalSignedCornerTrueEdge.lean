import Neoplatonic.LTR.SixDimensionalActualCornerOffDiagonal
import Neoplatonic.LTR.SixDimensionalSignedCoordinateThreeEdges
import Mathlib.Tactic

/-!
# LTR-MAN-132: true signed opposite corner equals undirected truth edge

The positive signed witness W=A+B has no same-truth-fibre
entries. Its 00/11 sector compression X=CWC is therefore
exactly the sum of the two oriented opposite truth blocks.

MAN-121 uses H=1/2 times that undirected edge in *both*
coordinate commutators. This module proves in the original
six-dimensional Dirac coordinates that H=X/2, allowing the
genuine saturated half-corner norm certificate to apply.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The true 00/11 corner compression contains precisely
the original positive witness's opposite undirected edge. -/
theorem sixLabelled_plusWitness_corner_eq_undirected03
    (label : Fin 6 → Fin 4) (D : SixMat) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    C * W * C = sixTruthUndirectedBlock label W 0 3 := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let P0 : SixMat := sixTruthFibreProjection label 0
  let P3 : SixMat := sixTruthFibreProjection label 3
  change C * W * C = P0 * W * P3 + P3 * W * P0
  have hC : C = P0 + P3 :=
    sixPlus_complement_eq_oppositeFibreProjections label
  have h00 : P0 * W * P0 = 0 :=
    sixLabelled_plusWitness_selfFibre_zero label D 0
  have h33 : P3 * W * P3 = 0 :=
    sixLabelled_plusWitness_selfFibre_zero label D 3
  calc
    C * W * C = (P0 + P3) * W * (P0 + P3) := by rw [hC]
    _ = P0 * W * P0 + P0 * W * P3 +
          P3 * W * P0 + P3 * W * P3 := by noncomm_ring
    _ = P0 * W * P3 + P3 * W * P0 := by
      rw [h00, h33]
      abel

/-- The active half-edge of MAN-121 is literally half the
genuine opposite-sector compression from MAN-124/129. -/
theorem sixLabelled_plusActiveHalf_eq_trueCornerHalf
    (label : Fin 6 → Fin 4) (D : SixMat) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    sixPlusActiveHalf label D =
      (1 / 2 : ℂ) • (C * W * C) := by
  dsimp only
  have hx := sixLabelled_plusWitness_corner_eq_undirected03 label D
  change
    (1 / 2 : ℂ) •
      sixTruthUndirectedBlock label
        (labelledSquareA label D + labelledSquareB label D) 0 3 =
    (1 / 2 : ℂ) •
      ((1 - sixTruthSectorProjection label squarePlusNeutral) *
        (labelledSquareA label D + labelledSquareB label D) *
        (1 - sixTruthSectorProjection label squarePlusNeutral))
  rw [hx]

end Neoplatonic.LTR
