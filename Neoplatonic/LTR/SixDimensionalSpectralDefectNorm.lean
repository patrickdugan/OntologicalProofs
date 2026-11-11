import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-143: the signed spectral defect controls corner-neutral leakage

In a nonsaturated signed six-dimensional witness W, MAN-140
identifies the failure of MAN-94's exact orthogonality XY=0 as
   XY = -C (I-W²) Q.

The genuine Hilbert operator norms of the complementary sector
projections C and Q are at most one. Consequently the
corner-to-neutral product has norm bounded by the full
spectral defect ||I-W²||. If that defect is at most 2ε,
then so is ||XY||.

The theorem is a reusable exact complex 6x6 C*-norm inequality;
the final labelled Dirac specialization is a separate step.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A spectrally defective, nearly involutive signed witness has
cross-channel leakage bounded by its spectral defect, assuming
the two sector projectors contract in Hilbert operator norm. -/
theorem sixMatrix_cornerNeutral_product_norm_le_defect
    (X Y C Q Δ : SixMat) (κ : ℝ)
    (hXY : X * Y = -(C * Δ * Q))
    (hC : ‖C‖ ≤ (1 : ℝ))
    (hQ : ‖Q‖ ≤ (1 : ℝ))
    (hκ : 0 ≤ κ)
    (hΔ : ‖Δ‖ ≤ κ) :
    ‖X * Y‖ ≤ κ := by
  have hCΔ : ‖C * Δ‖ ≤ κ := by
    calc
      ‖C * Δ‖ ≤ ‖C‖ * ‖Δ‖ := Matrix.l2_opNorm_mul C Δ
      _ ≤ (1 : ℝ) * κ :=
        mul_le_mul hC hΔ (norm_nonneg Δ) (by norm_num)
      _ = κ := one_mul _
  calc
    ‖X * Y‖ = ‖C * Δ * Q‖ := by rw [hXY, norm_neg]
    _ ≤ ‖C * Δ‖ * ‖Q‖ := Matrix.l2_opNorm_mul (C * Δ) Q
    _ ≤ κ * (1 : ℝ) :=
      mul_le_mul hCΔ hQ (norm_nonneg Q) hκ
    _ = κ := mul_one _

/-- Specialize the leakage gate to a spectral defect bounded by
twice the residual near-saturation slack. -/
theorem sixMatrix_cornerNeutral_product_norm_le_twoSlack
    (X Y C Q Δ : SixMat) (ε : ℝ)
    (hXY : X * Y = -(C * Δ * Q))
    (hC : ‖C‖ ≤ (1 : ℝ))
    (hQ : ‖Q‖ ≤ (1 : ℝ))
    (hε : 0 ≤ ε)
    (hΔ : ‖Δ‖ ≤ 2 * ε) :
    ‖X * Y‖ ≤ 2 * ε := by
  exact sixMatrix_cornerNeutral_product_norm_le_defect
    X Y C Q Δ (2 * ε) hXY hC hQ (by linarith) hΔ

end Neoplatonic.LTR
