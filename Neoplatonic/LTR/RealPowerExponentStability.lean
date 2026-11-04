import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Sharp uniform stability in a positive real exponent

The decay family `p ↦ exp (-h*p)` has Lipschitz constant
`1 / (exp 1 * δ)` on `p ≥ δ > 0`, uniformly over `h ≥ 0`.
The proof uses the exponential tangent inequality and the maximum
`t * exp (-t) ≤ exp (-1)`.

Substituting `h = -log x / 2` gives the half-exponent bound on
the entire interval `0 ≤ x ≤ 1`. The endpoint `x = 0` is proved
separately using the strict positivity of both exponents.
-/

namespace Neoplatonic.LTR

/-- A uniform envelope for the slope of an exponential decay family. -/
theorem decay_slope_le (h u δ : ℝ) (hh : 0 ≤ h)
    (hδ : 0 < δ) (hu : δ ≤ u) :
    h * Real.exp (-(h * u)) ≤ 1 / (Real.exp 1 * δ) := by
  have he : Real.exp (-(h * u)) ≤ Real.exp (-(δ * h)) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg hh (sub_nonneg.mpr hu)]
  have hm := Real.mul_exp_neg_le_exp_neg_one (δ * h)
  have hb : h * Real.exp (-(δ * h)) ≤ Real.exp (-1) / δ := by
    apply (le_div_iff₀ hδ).2
    nlinarith [hm]
  calc
    h * Real.exp (-(h * u)) ≤ h * Real.exp (-(δ * h)) :=
      mul_le_mul_of_nonneg_left he hh
    _ ≤ Real.exp (-1) / δ := hb
    _ = 1 / (Real.exp 1 * δ) := by
      simp [Real.exp_neg, div_eq_mul_inv, mul_inv_rev, mul_comm]

private theorem exp_neg_mul_sub_le_of_le
    (h p q δ : ℝ) (hh : 0 ≤ h) (hδ : 0 < δ)
    (hp : δ ≤ p) (hpq : p ≤ q) :
    Real.exp (-(h * p)) - Real.exp (-(h * q)) ≤
      (q - p) / (Real.exp 1 * δ) := by
  have ht : 1 - Real.exp (-((q - p) * h)) ≤ (q - p) * h := by
    linarith [Real.add_one_le_exp (-((q - p) * h))]
  have he : Real.exp (-(h * q)) =
      Real.exp (-(h * p)) * Real.exp (-((q - p) * h)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (-(h * p)) - Real.exp (-(h * q)) =
        Real.exp (-(h * p)) * (1 - Real.exp (-((q - p) * h))) := by
      rw [he]
      ring
    _ ≤ Real.exp (-(h * p)) * ((q - p) * h) :=
      mul_le_mul_of_nonneg_left ht (Real.exp_pos _).le
    _ = (q - p) * (h * Real.exp (-(h * p))) := by ring
    _ ≤ (q - p) * (1 / (Real.exp 1 * δ)) :=
      mul_le_mul_of_nonneg_left (decay_slope_le h p δ hh hδ hp)
        (sub_nonneg.mpr hpq)
    _ = (q - p) / (Real.exp 1 * δ) := by ring

/-- Exponential decay is uniformly Lipschitz in a positive exponent,
with a bound independent of the nonnegative decay rate. -/
theorem exp_neg_mul_sub_le
    (h p q δ : ℝ) (hh : 0 ≤ h) (hδ : 0 < δ)
    (hp : δ ≤ p) (hq : δ ≤ q) :
    |Real.exp (-(h * p)) - Real.exp (-(h * q))| ≤
      |p - q| / (Real.exp 1 * δ) := by
  have hordered (a b : ℝ) (ha : δ ≤ a) (hab : a ≤ b) :
      |Real.exp (-(h * a)) - Real.exp (-(h * b))| ≤
        |a - b| / (Real.exp 1 * δ) := by
    have hm : Real.exp (-(h * b)) ≤ Real.exp (-(h * a)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hh (sub_nonneg.mpr hab)]
    rw [abs_of_nonneg (sub_nonneg.mpr hm),
      abs_of_nonpos (sub_nonpos.mpr hab), neg_sub]
    exact exp_neg_mul_sub_le_of_le h a b δ hh hδ ha hab
  rcases le_total p q with hpq | hqp
  · exact hordered p q hp hpq
  · simpa only [abs_sub_comm] using hordered q p hq hqp

/-- Sharp uniform half-exponent stability for scalar positive contractions.
The estimate includes `x = 0` and is uniform over the entire unit interval. -/
theorem real_rpow_half_exponent_sub_le
    (x p q δ : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hδ : 0 < δ) (hp : δ ≤ p) (hq : δ ≤ q) :
    |x ^ (p / 2) - x ^ (q / 2)| ≤
      |p - q| / (Real.exp 1 * δ) := by
  rcases hx0.eq_or_lt with hx | hx
  · have hp0 : p / 2 ≠ 0 := ne_of_gt (by linarith)
    have hq0 : q / 2 ≠ 0 := ne_of_gt (by linarith)
    rw [← hx, Real.zero_rpow hp0, Real.zero_rpow hq0, sub_self, abs_zero]
    positivity
  · have hh : 0 ≤ -Real.log x / 2 := by
      have hlog := Real.log_nonpos hx.le hx1
      linarith
    rw [Real.rpow_def_of_pos hx (p / 2), Real.rpow_def_of_pos hx (q / 2),
      show Real.log x * (p / 2) = -((-Real.log x / 2) * p) by ring,
      show Real.log x * (q / 2) = -((-Real.log x / 2) * q) by ring]
    exact exp_neg_mul_sub_le (-Real.log x / 2) p q δ hh hδ hp hq

end Neoplatonic.LTR
