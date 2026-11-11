import Neoplatonic.LTR.SixDimensionalNearSaturatedPauliStability
import Mathlib.Tactic

/-!
# LTR-MAN-142: quantitative two-sign Pauli spectral defect near saturation

The genuine Pauli residual has real Gram coefficients q,r,c with
q,r >= 0, c² <= 4qr, and q+r+|c| <= 1. MAN-139 controls the
small signed combination q+r-|c| near the forbidden maximum
|c|=1/2.

The complementary signed witness has squared Pauli coefficient
q+r+|c|. Its involution defect is exactly
  Δ_res = 1-(q+r+|c|).

If |c| >= 1/2-ε, then 0 <= Δ_res <= 2ε.
The opposite signed witness has squared coefficient bounded by 2ε.
The inequalities are sign-refined: plus carries the near-involution
for c>=0, while minus does so for c<=0.

This is real algebra intended to combine with MAN-140's original
matrix defect Δ=I-W² and MAN-141's actual residual geometry.
-/

namespace Neoplatonic.LTR

/-- Near maximum positive overlap, the plus residual square is
within 2ε of the identity scalar, while the minus residual square
is at most 2ε. -/
theorem realGram_nearHalf_positive_signedDefects
    (q r c ε : ℝ)
    (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hdet : c ^ 2 ≤ 4 * q * r)
    (hbudget : q + r + |c| ≤ 1)
    (hc : 0 ≤ c)
    (hnear : (1 / 2 : ℝ) - ε ≤ |c|) :
    (0 ≤ 1 - (q + r + c) ∧
      1 - (q + r + c) ≤ 2 * ε) ∧
    (q + r - c ≤ 2 * ε) := by
  have hsq : |c| ^ 2 ≤ (q + r) ^ 2 := by
    rw [sq_abs]
    nlinarith [sq_nonneg (q - r)]
  have hcle : |c| ≤ q + r :=
    (sq_le_sq₀ (abs_nonneg _) (add_nonneg hq hr)).mp hsq
  rw [abs_of_nonneg hc] at hbudget hnear hcle
  constructor
  · constructor <;> linarith
  · linarith

/-- The mirrored negative overlap makes the minus residual an
approximate involution while the plus residual is small. -/
theorem realGram_nearHalf_negative_signedDefects
    (q r c ε : ℝ)
    (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hdet : c ^ 2 ≤ 4 * q * r)
    (hbudget : q + r + |c| ≤ 1)
    (hc : c ≤ 0)
    (hnear : (1 / 2 : ℝ) - ε ≤ |c|) :
    (0 ≤ 1 - (q + r - c) ∧
      1 - (q + r - c) ≤ 2 * ε) ∧
    (q + r + c ≤ 2 * ε) := by
  have hsq : |c| ^ 2 ≤ (q + r) ^ 2 := by
    rw [sq_abs]
    nlinarith [sq_nonneg (q - r)]
  have hcle : |c| ≤ q + r :=
    (sq_le_sq₀ (abs_nonneg _) (add_nonneg hq hr)).mp hsq
  rw [abs_of_nonpos hc] at hbudget hnear hcle
  constructor
  · constructor <;> linarith
  · linarith

/-- A sign-free near-boundary dichotomy: one signed witness is
near involutive and the other has small squared Pauli energy. -/
theorem realGram_nearHalf_signedDefect_dichotomy
    (q r c ε : ℝ)
    (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hdet : c ^ 2 ≤ 4 * q * r)
    (hbudget : q + r + |c| ≤ 1)
    (hnear : (1 / 2 : ℝ) - ε ≤ |c|) :
    ((0 ≤ 1 - (q + r + c) ∧
      1 - (q + r + c) ≤ 2 * ε) ∧
      q + r - c ≤ 2 * ε) ∨
    ((0 ≤ 1 - (q + r - c) ∧
      1 - (q + r - c) ≤ 2 * ε) ∧
      q + r + c ≤ 2 * ε) := by
  rcases le_total 0 c with hc | hc
  · left
    exact realGram_nearHalf_positive_signedDefects
      q r c ε hq hr hdet hbudget hc hnear
  · right
    exact realGram_nearHalf_negative_signedDefects
      q r c ε hq hr hdet hbudget hc hnear

end Neoplatonic.LTR
