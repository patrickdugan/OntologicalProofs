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

end Neoplatonic.LTR
