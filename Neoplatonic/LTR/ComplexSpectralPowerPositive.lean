import Neoplatonic.LTR.ComplexSpectralPowerSemigroup
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Genuine positive spectral powers on the infinite Dirac Hilbert space

Every positive real exponent gives an operator that is self-adjoint
and positive in Mathlib's actual continuous-Hilbert-operator sense.
The proof checks symmetry coordinatewise on ℓ²(ℕ, ℂ²) and then
uses the already verified exponent-halving identity A_(p/2)^2 = A_p
with positivity of B†B.

These statements are about the actual global complex Hilbert
operator, not merely finite block matrices or scalar weights.
-/

namespace Neoplatonic.LTR

open scoped lp InnerProductSpace

/-- The concrete positive spectral-power operator is self-adjoint
on the full infinite-dimensional complex Hilbert space. -/
theorem chosenComplexSpectralPower_isSelfAdjoint
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    IsSelfAdjoint (chosenComplexSpectralPowerCLM scale p hp) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro ψ φ
  simp only [lp.inner_eq_tsum]
  apply tsum_congr
  intro j
  change inner ℂ
      ((chosenComplexSpectralPowerCLM scale p hp ψ) j) (φ j) =
    inner ℂ (ψ j)
      ((chosenComplexSpectralPowerCLM scale p hp φ) j)
  rw [chosenComplexSpectralPowerCLM_apply,
    chosenComplexSpectralPowerCLM_apply]
  simp [inner_smul_left, inner_smul_right]

/-- Every A_p for p>0 is positive in Mathlib's operator sense. -/
theorem chosenComplexSpectralPower_isPositive
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    (chosenComplexSpectralPowerCLM scale p hp).IsPositive := by
  let B := chosenComplexSpectralPowerCLM scale (p / 2) (by linarith)
  have hB : IsSelfAdjoint B :=
    chosenComplexSpectralPower_isSelfAdjoint scale (p / 2) (by linarith)
  have hpos : (B.adjoint.comp B).IsPositive :=
    ContinuousLinearMap.isPositive_adjoint_comp_self B
  rw [hB.adjoint_eq] at hpos
  have hsquare : B.comp B = chosenComplexSpectralPowerCLM scale p hp := by
    exact chosenComplexSpectralPower_half_square scale p hp
  rw [hsquare] at hpos
  exact hpos

/-- The actual complex squared resolvent is positive. -/
theorem chosenComplexSquaredResolvent_isPositive
    (scale : ℕ → ℝ) :
    (chosenComplexSquaredResolventCLM scale).IsPositive := by
  rw [← chosenComplexSpectralPower_two_eq_squaredResolvent scale]
  exact chosenComplexSpectralPower_isPositive scale 2 (by norm_num)

/-- The actual complex squared resolvent is self-adjoint. -/
theorem chosenComplexSquaredResolvent_isSelfAdjoint
    (scale : ℕ → ℝ) :
    IsSelfAdjoint (chosenComplexSquaredResolventCLM scale) := by
  rw [← chosenComplexSpectralPower_two_eq_squaredResolvent scale]
  exact chosenComplexSpectralPower_isSelfAdjoint scale 2 (by norm_num)

end Neoplatonic.LTR
