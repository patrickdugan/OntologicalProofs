import Neoplatonic.LTR.ComplexSpectralPowerExponentContinuity

/-!
# Dyadic CFC approximants converge to the concrete real spectral powers

The preceding developments prove exact equality with Mathlib's
functional calculus at every positive dyadic rational exponent,
and genuine operator-norm continuity of A_p for p>0.

This module proves that *any* convergent sequence of positive
dyadic exponents has CFC operators converging in norm to the
concrete positive real spectral power A_p. It avoids choosing
a dyadic approximation algorithm and does not assume a general
CFC exponent-continuity theorem.
-/

namespace Neoplatonic.LTR

open scoped lp

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

/-- Any sequence of positive dyadic rationals converging to p/2
has genuine CFC powers converging in operator norm to A_p.
The integers n(i), m(i) encode k/2^n with k=m+1. -/
theorem chosenComplexSpectralDyadicRational_CFC_tendsto
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p)
    (n m : ℕ → ℕ)
    (hlimit : Filter.Tendsto
      (fun i : ℕ => complexSpectralDyadicExponent (n i) *
        (Nat.succ (m i) : ℝ)) Filter.atTop (nhds p)) :
    Filter.Tendsto
      (fun i : ℕ =>
        CFC.rpow (chosenComplexSquaredResolventCLM scale)
          (((1 / 2 : ℝ) ^ (n i)) * (Nat.succ (m i) : ℝ)))
      Filter.atTop
      (nhds (chosenComplexSpectralPowerCLM scale p hp)) := by
  have hcontinuous :
      ContinuousAt (chosenComplexSpectralPowerTotal scale) p :=
    (chosenComplexSpectralPowerTotal_continuousOn_positive scale p hp).continuousAt
      (Ici_mem_nhds (by linarith : p / 2 < p))
  have hterm :
      (fun i : ℕ =>
        CFC.rpow (chosenComplexSquaredResolventCLM scale)
          (((1 / 2 : ℝ) ^ (n i)) * (Nat.succ (m i) : ℝ))) =
      (fun i : ℕ =>
        chosenComplexSpectralPowerTotal scale
          (complexSpectralDyadicExponent (n i) *
            (Nat.succ (m i) : ℝ))) := by
    funext i
    have hpos : 0 < complexSpectralDyadicExponent (n i) *
        (Nat.succ (m i) : ℝ) := by
      have hn := complexSpectralDyadicExponent_pos (n i)
      positivity
    rw [chosenComplexSpectralPowerTotal_of_pos scale _ hpos]
    exact (chosenComplexSpectralDyadicRational_eq_CFC_rpow
      scale (n i) (m i)).symm
  rw [hterm]
  have h := hcontinuous.tendsto.comp hlimit
  simpa only [Function.comp_def,
    chosenComplexSpectralPowerTotal_of_pos scale p hp] using h

end Neoplatonic.LTR
