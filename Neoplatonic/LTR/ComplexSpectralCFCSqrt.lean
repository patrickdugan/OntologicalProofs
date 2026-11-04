import Neoplatonic.LTR.ComplexSpectralPowerPositive
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Continuous-functional-calculus square roots of concrete Dirac powers

The previous modules prove that the positive bounded Hilbert
operator A_(p/2) squares to A_p, and that A_(p/2) is positive
in Mathlib's operator order. The uniqueness theorem for the
positive CFC square root therefore identifies the two operators.

This is the first identification with Mathlib's genuine C⋆-algebra
functional calculus, rather than with a separately defined diagonal
power family.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- The actual Hilbert spectral power at half the exponent is the
positive CFC square root of the full power. -/
theorem chosenComplexSpectralPower_half_eq_CFC_sqrt
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    chosenComplexSpectralPowerCLM scale (p / 2) (by linarith) =
      CFC.sqrt (chosenComplexSpectralPowerCLM scale p hp) := by
  let B := chosenComplexSpectralPowerCLM scale (p / 2) (by linarith)
  have hB : (0 : ComplexDiracBlockHilbert →L[ℂ]
      ComplexDiracBlockHilbert) ≤ B := by
    simpa only [B, ContinuousLinearMap.le_def, sub_zero] using
      (chosenComplexSpectralPower_isPositive scale (p / 2) (by linarith))
  have hsq : B * B = chosenComplexSpectralPowerCLM scale p hp := by
    simpa only [B, ContinuousLinearMap.mul_def] using
      (chosenComplexSpectralPower_half_square scale p hp)
  exact (CFC.sqrt_unique hsq hB).symm

/-- The positive CFC square root of the actual two-sided complex
Dirac squared resolvent is precisely the p=1 spectral power. -/
theorem chosenComplexSpectralPower_one_eq_CFC_sqrt_resolvent
    (scale : ℕ → ℝ) :
    chosenComplexSpectralPowerCLM scale 1 (by norm_num) =
      CFC.sqrt (chosenComplexSquaredResolventCLM scale) := by
  rw [← chosenComplexSpectralPower_two_eq_squaredResolvent scale]
  simpa only [show (2 : ℝ) / 2 = 1 by norm_num] using
    (chosenComplexSpectralPower_half_eq_CFC_sqrt scale 2 (by norm_num))

end Neoplatonic.LTR
