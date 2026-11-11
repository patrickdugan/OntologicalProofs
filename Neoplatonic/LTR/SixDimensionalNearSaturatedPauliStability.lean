import Neoplatonic.LTR.SixDimensionalPauliSharpHalf
import Mathlib.Tactic

/-!
# LTR-MAN-139: quantitative stability near maximal residual Pauli overlap

MAN-138 excludes the endpoint |c| = 1/2 in genuine exact-Hamming
six-dimensional Dirac charts. The next objective is to control
nonsaturated Pauli residuals uniformly near that forbidden boundary.

For real Gram data q,r,c with q,r >= 0, c² <= 4qr, and
q+r+|c| <= 1, let ε >= 0 with |c| >= 1/2 - ε.

The Pauli Gram bounds force
  |(q+r)-1/2| <= ε,
  (q-r)² <= 2ε,
  min(q+r+c, q+r-c) <= 2ε.

The last expression is the smaller squared norm of the two
residual signed witnesses M+N or M-N for Hermitian traceless
2x2 Pauli matrices. The preceding two bounds force the lengths
of those residual matrices toward 1/4 as ε tends to zero.

These are exact real-algebraic lemmas and admit straightforward
specialization to the actual complex six-dimensional residual
system; no false dimension lower bound is inferred.
-/

namespace Neoplatonic.LTR

/-- Near maximal signed Pauli overlap, one of the two signed
residual quadratic energies is at most twice the slack. -/
theorem realGram_nearHalf_oneSignedEnergy_small
    (q r c ε : ℝ)
    (hbudget : q + r + |c| ≤ 1)
    (hnear : (1 / 2 : ℝ) - ε ≤ |c|) :
    q + r + c ≤ 2 * ε ∨ q + r - c ≤ 2 * ε := by
  rcases le_total 0 c with hc | hc
  · right
    rw [abs_of_nonneg hc] at hbudget hnear
    linarith
  · left
    rw [abs_of_nonpos hc] at hbudget hnear
    linarith

/-- Near-saturation controls the sum of the two residual real
Pauli quadratic lengths to within the overlap slack. -/
theorem realGram_nearHalf_sum_length_near_quarter
    (q r c ε : ℝ)
    (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hdet : c ^ 2 ≤ 4 * q * r)
    (hbudget : q + r + |c| ≤ 1)
    (hnear : (1 / 2 : ℝ) - ε ≤ |c|) :
    (1 / 2 : ℝ) - ε ≤ q + r ∧
      q + r ≤ (1 / 2 : ℝ) + ε := by
  have hsq : |c| ^ 2 ≤ (q + r) ^ 2 := by
    rw [sq_abs]
    nlinarith [sq_nonneg (q - r)]
  have hle : |c| ≤ q + r :=
    (sq_le_sq₀ (abs_nonneg _) (add_nonneg hq hr)).mp hsq
  constructor <;> linarith

/-- The squared difference between the real Pauli quadratic
lengths is controlled by twice the distance to maximal overlap. -/
theorem realGram_nearHalf_length_difference_sq_le
    (q r c ε : ℝ)
    (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hdet : c ^ 2 ≤ 4 * q * r)
    (hbudget : q + r + |c| ≤ 1)
    (hnear : (1 / 2 : ℝ) - ε ≤ |c|) :
    (q - r) ^ 2 ≤ 2 * ε := by
  have hsumNonneg : 0 ≤ q + r := add_nonneg hq hr
  have hsumBound : q + r ≤ 1 - |c| := by linarith
  have hRestNonneg : 0 ≤ 1 - |c| := by linarith
  have hprod :
      0 ≤ ((1 - |c|) - (q + r)) * ((1 - |c|) + (q + r)) :=
    mul_nonneg (by linarith) (by linarith)
  have hsumSquare : (q + r) ^ 2 ≤ (1 - |c|) ^ 2 := by
    nlinarith [hprod]
  have habsSquare : |c| ^ 2 = c ^ 2 := sq_abs c
  have hgap : (q - r) ^ 2 ≤ 1 - 2 * |c| := by
    nlinarith [hsumSquare, hdet, habsSquare]
  linarith

end Neoplatonic.LTR
