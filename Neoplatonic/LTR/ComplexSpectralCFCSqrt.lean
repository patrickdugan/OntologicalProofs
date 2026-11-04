import Neoplatonic.LTR.ComplexSpectralPowerPositive
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
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

-- The pinned Mathlib constructors expose these CFC instances explicitly.
-- Register them locally for the concrete infinite Hilbert operator algebra.
local instance :
    NonUnitalClosedEmbeddingContinuousFunctionalCalculus ℂ
      (ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert)
      IsStarNormal :=
  IsStarNormal.instNonUnitalContinuousFunctionalCalculus

local instance :
    NonUnitalContinuousFunctionalCalculus ℝ
      (ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert)
      IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

-- The unital CFC is needed for real operator powers.
local instance :
    ContinuousFunctionalCalculus ℂ
      (ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert)
      IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

local instance :
    ContinuousFunctionalCalculus ℝ
      (ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert)
      IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

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

/-- The CFC square-root identity is also a genuine real-power
functional-calculus identity at exponent one half. -/
theorem chosenComplexSpectralPower_half_eq_CFC_rpow_half
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    chosenComplexSpectralPowerCLM scale (p / 2) (by linarith) =
      CFC.rpow (chosenComplexSpectralPowerCLM scale p hp) (1 / 2 : ℝ) := by
  simpa only [CFC.sqrt_eq_rpow, CFC.rpow_eq_pow] using
    (chosenComplexSpectralPower_half_eq_CFC_sqrt scale p hp)

/-- The p=1 operator equals the actual CFC real square-root power
of the full bounded Dirac squared resolvent. -/
theorem chosenComplexSpectralPower_one_eq_CFC_rpow_half_resolvent
    (scale : ℕ → ℝ) :
    chosenComplexSpectralPowerCLM scale 1 (by norm_num) =
      CFC.rpow (chosenComplexSquaredResolventCLM scale) (1 / 2 : ℝ) := by
  simpa only [CFC.sqrt_eq_rpow, CFC.rpow_eq_pow] using
    (chosenComplexSpectralPower_one_eq_CFC_sqrt_resolvent scale)


/-- The positive exponents obtained by repeated halving of two. -/
def complexSpectralDyadicExponent : ℕ → ℝ
  | 0 => 2
  | n + 1 => complexSpectralDyadicExponent n / 2

/-- Each dyadic exponent is strictly positive. -/
theorem complexSpectralDyadicExponent_pos (n : ℕ) :
    0 < complexSpectralDyadicExponent n := by
  induction n with
  | zero => norm_num [complexSpectralDyadicExponent]
  | succ n ih =>
      simpa only [complexSpectralDyadicExponent] using
        (div_pos ih (by norm_num : (0 : ℝ) < 2))

/-- Repeated CFC square roots of the actual squared resolvent. -/
noncomputable def chosenComplexSpectralDyadicSqrt
    (scale : ℕ → ℝ) :
    ℕ → (ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert)
  | 0 => chosenComplexSquaredResolventCLM scale
  | n + 1 => CFC.sqrt (chosenComplexSpectralDyadicSqrt scale n)

/-- The iterated CFC square roots agree with the actual global
Hilbert spectral powers at every strictly positive dyadic exponent. -/
theorem chosenComplexSpectralDyadicSqrt_eq
    (scale : ℕ → ℝ) (n : ℕ) :
    chosenComplexSpectralDyadicSqrt scale n =
      chosenComplexSpectralPowerCLM scale
        (complexSpectralDyadicExponent n)
        (complexSpectralDyadicExponent_pos n) := by
  induction n with
  | zero =>
      simpa only [chosenComplexSpectralDyadicSqrt,
        complexSpectralDyadicExponent] using
        (chosenComplexSpectralPower_two_eq_squaredResolvent scale).symm
  | succ n ih =>
      change CFC.sqrt (chosenComplexSpectralDyadicSqrt scale n) = _
      rw [ih]
      simpa only [complexSpectralDyadicExponent] using
        (chosenComplexSpectralPower_half_eq_CFC_sqrt
          scale (complexSpectralDyadicExponent n)
          (complexSpectralDyadicExponent_pos n)).symm

/-- Closed formula for the verified dyadic spectral exponents. -/
theorem complexSpectralDyadicExponent_eq (n : ℕ) :
    complexSpectralDyadicExponent n = 2 / (2 : ℝ) ^ n := by
  induction n with
  | zero => norm_num [complexSpectralDyadicExponent]
  | succ n ih =>
      rw [complexSpectralDyadicExponent, ih, pow_succ, div_mul_eq_div_div]

end Neoplatonic.LTR
