import Neoplatonic.LTR.ComplexSpectralRankTwoCertificate

/-!
# Positive spectral powers form a semigroup

The concrete complex Hilbert-space operators satisfy the
multiplicative law for every pair of positive real exponents.
The p=2 family member is the maximal-domain squared resolvent.

The statement is an operator identity, not an invocation of a
general unbounded functional calculus.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Strict positivity of every squared-resolvent weight. -/
theorem chosenSquaredResolventWeight_pos
    (scale : ℕ → ℝ) (j : ℕ) :
    0 < chosenSquaredResolventWeight scale j := by
  unfold chosenSquaredResolventWeight
  positivity

/-- Positive spectral weights multiply according to their real exponents. -/
theorem complexSpectralPowerWeight_add
    (scale : ℕ → ℝ) (p q : ℝ) (j : ℕ) :
    complexSpectralPowerWeight scale (p + q) j =
      complexSpectralPowerWeight scale p j *
      complexSpectralPowerWeight scale q j := by
  unfold complexSpectralPowerWeight
  rw [show (p + q) / 2 = p / 2 + q / 2 by ring]
  exact Real.rpow_add (chosenSquaredResolventWeight_pos scale j) _ _

/-- Semigroup law for the actual infinite-dimensional bounded complex
Hilbert operators, for arbitrary strictly positive real exponents. -/
theorem chosenComplexSpectralPower_comp
    (scale : ℕ → ℝ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (chosenComplexSpectralPowerCLM scale p hp).comp
      (chosenComplexSpectralPowerCLM scale q hq) =
        chosenComplexSpectralPowerCLM scale (p + q) (by linarith) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  rw [ContinuousLinearMap.comp_apply,
    chosenComplexSpectralPowerCLM_apply,
    chosenComplexSpectralPowerCLM_apply,
    chosenComplexSpectralPowerCLM_apply]
  rw [smul_smul, complexSpectralPowerWeight_add]
  simp only [Complex.ofReal_mul]

/-- Every pair of positive spectral powers commutes as Hilbert operators. -/
theorem chosenComplexSpectralPower_comp_comm
    (scale : ℕ → ℝ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    (chosenComplexSpectralPowerCLM scale p hp).comp
      (chosenComplexSpectralPowerCLM scale q hq) =
    (chosenComplexSpectralPowerCLM scale q hq).comp
      (chosenComplexSpectralPowerCLM scale p hp) := by
  rw [chosenComplexSpectralPower_comp, chosenComplexSpectralPower_comp]
  congr 1
  exact add_comm p q

/-- A positive power at half an exponent squares to the full power. -/
theorem chosenComplexSpectralPower_half_square
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    (chosenComplexSpectralPowerCLM scale (p / 2) (by linarith)).comp
      (chosenComplexSpectralPowerCLM scale (p / 2) (by linarith)) =
        chosenComplexSpectralPowerCLM scale p hp := by
  simpa only [add_halves] using
    (chosenComplexSpectralPower_comp scale (p / 2) (p / 2)
      (by linarith) (by linarith))

/-- The p=1 spectral power is a genuine operator square root of
the complex maximal-domain squared resolvent. -/
theorem chosenComplexSpectralPower_one_square
    (scale : ℕ → ℝ) :
    (chosenComplexSpectralPowerCLM scale 1 (by norm_num)).comp
      (chosenComplexSpectralPowerCLM scale 1 (by norm_num)) =
        chosenComplexSquaredResolventCLM scale := by
  have hcomp :
      (chosenComplexSpectralPowerCLM scale 1 (by norm_num)).comp
        (chosenComplexSpectralPowerCLM scale 1 (by norm_num)) =
      chosenComplexSpectralPowerCLM scale 2 (by norm_num) := by
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using
      (chosenComplexSpectralPower_comp scale 1 1
        (by norm_num) (by norm_num))
  exact hcomp.trans
    (chosenComplexSpectralPower_two_eq_squaredResolvent scale)

end Neoplatonic.LTR
