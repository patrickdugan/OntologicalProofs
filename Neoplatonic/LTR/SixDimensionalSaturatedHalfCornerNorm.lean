import Neoplatonic.LTR.SixDimensionalActualCornerOffDiagonal
import Neoplatonic.LTR.SixDimensionalTriple03ProbeHammingNoGo
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-129: true positive-saturated half-corner is a half contraction

The real six-dimensional positive signed witness W=A+B is a
Hermitian involution at the maximal opposite-corner saturation.
Therefore its genuine Euclidean operator norm is exactly one.

The opposite corner C=1-Q is a diagonal 0/1 projection, with
operator norm at most one. The actual corner compression X=CWC
is consequently a contraction and its half-size contribution
to either coordinate has norm at most 1/2.

This is a basis-free direct route to the active-channel
hypothesis of MAN-120's Hermitian three-channel C*-norm gate.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Every complementary diagonal truth-sector projector is a
Hilbert operator contraction, regardless of fibre multiplicities. -/
theorem sixTruthSectorProjection_complement_norm_le_one
    (label : Fin 6 → Fin 4)
    (sector : Fin 4 → Prop) [DecidablePred sector] :
    ‖(1 : SixMat) - sixTruthSectorProjection label sector‖ ≤ 1 := by
  have hdiag :
      (1 : SixMat) - sixTruthSectorProjection label sector =
        Matrix.diagonal (fun i : Fin 6 =>
          if sector (label i) then (0 : ℂ) else 1) := by
    ext i j
    by_cases hij : i = j
    · subst j
      by_cases hi : sector (label i)
      · simp [sixTruthSectorProjection, Matrix.sub_apply,
          Matrix.one_apply, Matrix.diagonal_apply, hi]
      · simp [sixTruthSectorProjection, Matrix.sub_apply,
          Matrix.one_apply, Matrix.diagonal_apply, hi]
    · simp [sixTruthSectorProjection, Matrix.sub_apply,
        Matrix.one_apply, Matrix.diagonal_apply, hij]
  rw [hdiag, Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  by_cases hi : sector (label i) <;> simp [hi]

/-- Compressing a contraction through any Hilbert operator
contraction preserves the unit operator-norm bound. -/
theorem sixMatrix_twoSidedCompression_norm_le_one
    (C W : SixMat)
    (hC : ‖C‖ ≤ (1 : ℝ))
    (hW : ‖W‖ ≤ (1 : ℝ)) :
    ‖C * W * C‖ ≤ (1 : ℝ) := by
  have hCW : ‖C * W‖ ≤ (1 : ℝ) := by
    calc
      ‖C * W‖ ≤ ‖C‖ * ‖W‖ := Matrix.l2_opNorm_mul C W
      _ ≤ (1 : ℝ) * 1 :=
        mul_le_mul hC hW (norm_nonneg W) (by norm_num)
      _ = 1 := by ring
  calc
    ‖C * W * C‖ ≤ ‖C * W‖ * ‖C‖ :=
      Matrix.l2_opNorm_mul (C * W) C
    _ ≤ (1 : ℝ) * 1 :=
      mul_le_mul hCW hC (norm_nonneg C) (by norm_num)
    _ = 1 := by ring

/-- The actual original-coordinate positive saturated signed
corner has a half-size component with norm at most 1/2.
This is independent of a U(2) basis choice or Gram chart. -/
theorem sixLabelled_exactHamming_saturated03_halfCorner_norm_le
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
    ‖(1 / 2 : ℂ) • (C * W * C)‖ ≤ (1 / 2 : ℝ) := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  change ‖(1 / 2 : ℂ) • (C * W * C)‖ ≤ (1 / 2 : ℝ)
  have hW : W * W = 1 :=
    sixLabelled_exactHamming_saturated03_trueMatrixPlus_involution
      label D hD hham h03 h12
  have hWH : W.IsHermitian :=
    sixLabelled_plusWitness_isHermitian label D hD
  have hWnorm : ‖W‖ = (1 : ℝ) :=
    sixMatrix_hermitianInvolution_operatorNorm_one W hWH hW
  have hC : ‖C‖ ≤ (1 : ℝ) :=
    sixTruthSectorProjection_complement_norm_le_one
      label squarePlusNeutral
  have hCorner : ‖C * W * C‖ ≤ (1 : ℝ) :=
    sixMatrix_twoSidedCompression_norm_le_one C W hC (le_of_eq hWnorm)
  rw [norm_smul]
  have hscalar : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hscalar]
  nlinarith

end Neoplatonic.LTR
