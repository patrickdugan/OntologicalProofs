import Neoplatonic.LTR.RealPowerExponentStability
import Neoplatonic.LTR.ComplexSpectralPowerStability
import Neoplatonic.LTR.ComplexSpectralCFCReal

/-!
# Quantitative exponent stability of the Dirac functional calculus

On every exponent half-line p,q ≥ δ > 0, the actual Hilbert
spectral powers satisfy ‖A_p - A_q‖ ≤ |p-q| / (exp 1 * δ).
The scalar estimate is uniform over all squared-resolvent weights
in [0,1]. The verified diagonal norm estimate lifts it to the whole
infinite Hilbert space, for arbitrary real edge couplings.

The full positive-real CFC identity then gives the same estimate
for Mathlib's genuine powers of the squared resolvent.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Uniform exponent bound for every Dirac weight, inherited from
the sharp scalar estimate on the unit interval. -/
theorem complexSpectralPowerWeight_sub_le
    (scale : ℕ → ℝ) (p q δ : ℝ) (hδ : 0 < δ)
    (hp : δ ≤ p) (hq : δ ≤ q) (j : ℕ) :
    |complexSpectralPowerWeight scale p j -
      complexSpectralPowerWeight scale q j| ≤
      |p - q| / (Real.exp 1 * δ) := by
  exact real_rpow_half_exponent_sub_le
    (chosenSquaredResolventWeight scale j) p q δ
    (chosenSquaredResolventWeight_nonneg scale j)
    (chosenSquaredResolventWeight_le_one scale j) hδ hp hq

/-- Uniform operator-norm Lipschitz estimate on every positive
exponent half-line, with a constant independent of the couplings. -/
theorem chosenComplexSpectralPower_sub_norm_le_lipschitz
    (scale : ℕ → ℝ) (p q δ : ℝ) (hδ : 0 < δ)
    (hp : δ ≤ p) (hq : δ ≤ q) :
    ‖chosenComplexSpectralPowerCLM scale p (lt_of_lt_of_le hδ hp) -
      chosenComplexSpectralPowerCLM scale q (lt_of_lt_of_le hδ hq)‖ ≤
      |p - q| / (Real.exp 1 * δ) := by
  apply chosenComplexSpectralPower_sub_norm_le
    scale p q (lt_of_lt_of_le hδ hp) (lt_of_lt_of_le hδ hq)
    (|p - q| / (Real.exp 1 * δ)) (by positivity)
  exact complexSpectralPowerWeight_sub_le scale p q δ hδ hp hq

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

/-- The same quantitative bound holds for the genuine Mathlib CFC
real powers of the actual infinite-dimensional squared resolvent. -/
theorem chosenComplexSquaredResolvent_CFC_rpow_sub_norm_le
    (scale : ℕ → ℝ) (p q δ : ℝ) (hδ : 0 < δ)
    (hp : δ ≤ p) (hq : δ ≤ q) :
    ‖CFC.rpow (chosenComplexSquaredResolventCLM scale) (p / 2) -
      CFC.rpow (chosenComplexSquaredResolventCLM scale) (q / 2)‖ ≤
      |p - q| / (Real.exp 1 * δ) := by
  rw [← chosenComplexSpectralPower_eq_CFC_rpow
      scale p (lt_of_lt_of_le hδ hp),
    ← chosenComplexSpectralPower_eq_CFC_rpow
      scale q (lt_of_lt_of_le hδ hq)]
  exact chosenComplexSpectralPower_sub_norm_le_lipschitz scale p q δ hδ hp hq

end Neoplatonic.LTR
