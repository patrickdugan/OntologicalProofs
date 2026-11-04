import Neoplatonic.LTR.ComplexSpectralCFCSqrt

/-!
# Positive dyadic-rational functional-calculus identification

The preceding module identifies A_(2/2^n) with the real
continuous-functional-calculus power R^(1/2^n). Repeated multiplication
extends this identity from unit dyadic numerators to every positive
integer numerator. All equalities are on the full complex Hilbert
space, not only on finite-dimensional spectral blocks.
-/

namespace Neoplatonic.LTR

open scoped lp

-- Register the pinned Mathlib CFC constructors for this operator type.
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

/-- The natural power of a positive spectral-power operator is the
spectral-power operator at the corresponding positive multiple. -/
theorem chosenComplexSpectralPower_pow_nat_succ
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) (n : ℕ) :
    (chosenComplexSpectralPowerCLM scale p hp) ^ (Nat.succ n) =
      chosenComplexSpectralPowerCLM scale
        (p * (Nat.succ n : ℝ)) (by positivity) := by
  induction n with
  | zero =>
      simp only [Nat.succ_eq_add_one, zero_add, pow_one,
        Nat.cast_one, mul_one]
  | succ n ih =>
      have hn : 0 < p * (Nat.succ n : ℝ) := by positivity
      calc
        (chosenComplexSpectralPowerCLM scale p hp) ^
            Nat.succ (Nat.succ n) =
          (chosenComplexSpectralPowerCLM scale p hp) ^
              (Nat.succ n) * chosenComplexSpectralPowerCLM scale p hp := by
                rw [pow_succ]
        _ = chosenComplexSpectralPowerCLM scale
              (p * (Nat.succ n : ℝ)) (by positivity) *
              chosenComplexSpectralPowerCLM scale p hp := by rw [ih]
        _ = chosenComplexSpectralPowerCLM scale
              (p * (Nat.succ n : ℝ) + p) (by positivity) := by
                simpa only [ContinuousLinearMap.mul_def] using
                  (chosenComplexSpectralPower_comp scale
                    (p * (Nat.succ n : ℝ)) p hn hp)
        _ = chosenComplexSpectralPowerCLM scale
              (p * (Nat.succ (Nat.succ n) : ℝ)) (by positivity) := by
                congr 1
                push_cast
                ring

/-- Every positive dyadic-rational exponent k/2^n in the CFC
corresponds to the genuine Hilbert spectral power at 2k/2^n.
Here k = Nat.succ m, ensuring strict positivity. -/
theorem chosenComplexSpectralDyadicRational_eq_CFC_rpow
    (scale : ℕ → ℝ) (n m : ℕ) :
    chosenComplexSpectralPowerCLM scale
      (complexSpectralDyadicExponent n * (Nat.succ m : ℝ))
      (by exact mul_pos (complexSpectralDyadicExponent_pos n)
        (by positivity)) =
      CFC.rpow (chosenComplexSquaredResolventCLM scale)
        (((1 / 2 : ℝ) ^ n) * (Nat.succ m : ℝ)) := by
  let R := chosenComplexSquaredResolventCLM scale
  let x : ℝ := (1 / 2 : ℝ) ^ n
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy : 0 ≤ (Nat.succ m : ℝ) := by positivity
  have hR : (0 : ComplexDiracBlockHilbert →L[ℂ]
      ComplexDiracBlockHilbert) ≤ R := by
    simpa only [R, ContinuousLinearMap.le_def, sub_zero] using
      (chosenComplexSquaredResolvent_isPositive scale)
  have hRP : (0 : ComplexDiracBlockHilbert →L[ℂ]
      ComplexDiracBlockHilbert) ≤ CFC.rpow R x :=
    CFC.rpow_nonneg
  have hnat :
      (CFC.rpow R x) ^ (Nat.succ m) =
      CFC.rpow (CFC.rpow R x) (Nat.succ m : ℝ) := by
    simpa only [CFC.rpow_eq_pow] using
      (CFC.rpow_natCast (CFC.rpow R x) (Nat.succ m) hRP).symm
  have hpower :
      (CFC.rpow R x) ^ (Nat.succ m) =
      CFC.rpow R (x * (Nat.succ m : ℝ)) := by
    rw [hnat]
    simpa only [CFC.rpow_eq_pow] using
      (CFC.rpow_rpow_of_exponent_nonneg R x (Nat.succ m : ℝ)
        hx hy hR)
  calc
    chosenComplexSpectralPowerCLM scale
        (complexSpectralDyadicExponent n * (Nat.succ m : ℝ))
        (by exact mul_pos (complexSpectralDyadicExponent_pos n)
          (by positivity)) =
      (chosenComplexSpectralPowerCLM scale
        (complexSpectralDyadicExponent n)
        (complexSpectralDyadicExponent_pos n)) ^ (Nat.succ m) := by
          exact (chosenComplexSpectralPower_pow_nat_succ scale
            (complexSpectralDyadicExponent n)
            (complexSpectralDyadicExponent_pos n) m).symm
    _ = (CFC.rpow R x) ^ (Nat.succ m) := by
          rw [chosenComplexSpectralDyadicPower_eq_CFC_rpow]
    _ = CFC.rpow R (x * (Nat.succ m : ℝ)) := hpower
    _ = CFC.rpow (chosenComplexSquaredResolventCLM scale)
          (((1 / 2 : ℝ) ^ n) * (Nat.succ m : ℝ)) := rfl

end Neoplatonic.LTR
