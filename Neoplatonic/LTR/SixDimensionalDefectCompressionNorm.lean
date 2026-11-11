import Neoplatonic.LTR.SixDimensionalNonSaturatedCornerDefect
import Neoplatonic.LTR.SixDimensionalSaturatedHalfCornerNorm
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-143: quantitative cross-channel defect control

The nonsaturated MAN-140 signed block identities express the
failure of corner-neutral annihilation XY=0 as a compression
of the original residual spectral defect Δ=I-W².

For any Euclidean-contractive projectors C and Q,
  XY = -CΔQ,
  YᴴY-Q = -QΔQ
give the certified operator norm inequalities
  ||XY|| ≤ ||Δ||,    ||YᴴY-Q|| ≤ ||Δ||.

This applies to the actual labelled Dirac witness W=A+B
without an opposite energy saturation hypothesis or a choice
of canonical U(2) basis.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Compressing an arbitrary matrix between two Euclidean
operator contractions cannot increase its operator norm. -/
theorem sixMatrix_twoContraction_compression_norm_le
    (C Q Δ : SixMat)
    (hC : ‖C‖ ≤ (1 : ℝ))
    (hQ : ‖Q‖ ≤ (1 : ℝ)) :
    ‖C * Δ * Q‖ ≤ ‖Δ‖ := by
  have hCD : ‖C * Δ‖ ≤ ‖Δ‖ := by
    calc
      ‖C * Δ‖ ≤ ‖C‖ * ‖Δ‖ := Matrix.l2_opNorm_mul C Δ
      _ ≤ (1 : ℝ) * ‖Δ‖ :=
        mul_le_mul_of_nonneg_right hC (norm_nonneg Δ)
      _ = ‖Δ‖ := by ring
  calc
    ‖C * Δ * Q‖ ≤ ‖C * Δ‖ * ‖Q‖ :=
      Matrix.l2_opNorm_mul (C * Δ) Q
    _ ≤ ‖C * Δ‖ * (1 : ℝ) :=
      mul_le_mul_of_nonneg_left hQ (norm_nonneg (C * Δ))
    _ = ‖C * Δ‖ := by ring
    _ ≤ ‖Δ‖ := hCD

/-- The labelled six-dimensional truth-sector diagonal projector
has Euclidean operator norm at most one. -/
theorem sixTruthSectorProjection_generic_norm_le_one
    (label : Fin 6 → Fin 4)
    (sector : Fin 4 → Prop) [DecidablePred sector] :
    ‖sixTruthSectorProjection label sector‖ ≤ (1 : ℝ) := by
  change ‖(Matrix.diagonal
    (fun i : Fin 6 => if sector (label i) then (1 : ℂ) else 0) :
      SixMat)‖ ≤ (1 : ℝ)
  rw [Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  by_cases hi : sector (label i) <;> simp [hi]

/-- The genuine signed Hamming Dirac corner-neutral interaction
and neutral partial-isometry defect are both bounded by the
actual six-dimensional signed spectral defect I-W². -/
theorem sixLabelled_plusWitness_nonSaturated_normDefect
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    let X := C * W * C
    let Y := C * W * Q
    let Δ := (1 : SixMat) - W * W
    ‖X * Y‖ ≤ ‖Δ‖ ∧
      ‖Y.conjTranspose * Y - Q‖ ≤ ‖Δ‖ := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let X : SixMat := C * W * C
  let Y : SixMat := C * W * Q
  let Δ : SixMat := 1 - W * W
  change ‖X * Y‖ ≤ ‖Δ‖ ∧
    ‖Y.conjTranspose * Y - Q‖ ≤ ‖Δ‖
  have hBlock := sixLabelled_plusWitness_nonSaturated_blockDefect
    label D hD
  change X * X + Y * Y.conjTranspose = C - C * Δ * C ∧
    X * Y = -(C * Δ * Q) ∧
    Y.conjTranspose * Y = Q - Q * Δ * Q at hBlock
  have hC : ‖C‖ ≤ (1 : ℝ) :=
    sixTruthSectorProjection_complement_norm_le_one
      label squarePlusNeutral
  have hQ : ‖Q‖ ≤ (1 : ℝ) :=
    sixTruthSectorProjection_generic_norm_le_one
      label squarePlusNeutral
  have hXY : X * Y = -(C * Δ * Q) := hBlock.2.1
  have hYY : Y.conjTranspose * Y = Q - Q * Δ * Q :=
    hBlock.2.2
  constructor
  · calc
      ‖X * Y‖ = ‖C * Δ * Q‖ := by rw [hXY, norm_neg]
      _ ≤ ‖Δ‖ :=
        sixMatrix_twoContraction_compression_norm_le C Q Δ hC hQ
  · have hSubtract :
        Y.conjTranspose * Y - Q = -(Q * Δ * Q) := by
      rw [hYY]
      abel
    calc
      ‖Y.conjTranspose * Y - Q‖ = ‖Q * Δ * Q‖ := by
        rw [hSubtract, norm_neg]
      _ ≤ ‖Δ‖ :=
        sixMatrix_twoContraction_compression_norm_le Q Q Δ hQ hQ

end Neoplatonic.LTR
