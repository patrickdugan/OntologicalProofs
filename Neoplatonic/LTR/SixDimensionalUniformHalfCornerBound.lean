import Neoplatonic.LTR.SixDimensionalSaturatedHalfCornerNorm
import Neoplatonic.LTR.SixDimensionalSignedCornerTrueEdge
import Neoplatonic.LTR.SixDimensionalExactHammingPauliSaturation
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-157: the active opposite-corner half-edge is always a contraction

The original six-dimensional exact-Hamming metric produces both
canonical signed witness contractions, independent of Pauli
saturation. Hence the actual complex matrix W=A+B has norm <=1.

Every complementary diagonal truth-sector projection C=1-Q is a
Euclidean operator contraction. Therefore its compression X=CWC
has norm at most one. The active 00/11 half-edge of either
coordinate H=1/2 X consequently satisfies ||H||<=1/2.

This discharges MAN-153/155's shared-corner norm hypothesis across
the entire nonsaturated region of the original labelled Dirac chart.
No saturated energy or U(2) gauge is assumed.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Both canonical signed coordinate witnesses are genuine
operator contractions in every exact-Hamming six-dimensional chart,
in the original Hilbert matrix norm. -/
theorem sixLabelled_exactHamming_plusWitness_norm_le_one
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    ‖labelledSquareA label D + labelledSquareB label D‖ ≤ (1 : ℝ) := by
  obtain ⟨S, _, hA, hB, _, _⟩ :=
    sixLabelled_exactHamming_oppositeEnergy_budget label D hD hham
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  have hmap : W.toEuclideanLin.toContinuousLinearMap =
      sixLabelledAOperator label D + sixLabelledBOperator label D := by
    change (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)) W =
      (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
        (labelledSquareA label D) +
      (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
        (labelledSquareB label D)
    exact map_add (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)) _ _
  change ‖W‖ ≤ (1 : ℝ)
  rw [Matrix.cstar_norm_def]
  change ‖W.toEuclideanLin.toContinuousLinearMap‖ ≤ (1 : ℝ)
  rw [hmap, ← hA, ← hB]
  exact S.plus_le

/-- The genuine common 00/11 half-corner of the two coordinate
operators is bounded by one half throughout the unsaturated
six-dimensional exact-Hamming region. -/
theorem sixLabelled_exactHamming_plusActiveHalf_norm_le
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    ‖sixPlusActiveHalf label D‖ ≤ (1 / 2 : ℝ) := by
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  have hW : ‖W‖ ≤ (1 : ℝ) :=
    sixLabelled_exactHamming_plusWitness_norm_le_one
      label D hD hham
  have hC : ‖C‖ ≤ (1 : ℝ) :=
    sixTruthSectorProjection_complement_norm_le_one
      label squarePlusNeutral
  have hCorner : ‖C * W * C‖ ≤ (1 : ℝ) :=
    sixMatrix_twoSidedCompression_norm_le_one C W hC hW
  have hHalf : sixPlusActiveHalf label D =
      (1 / 2 : ℂ) • (C * W * C) :=
    sixLabelled_plusActiveHalf_eq_trueCornerHalf label D
  rw [hHalf, norm_smul]
  have hscalar : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hscalar]
  nlinarith

end Neoplatonic.LTR
