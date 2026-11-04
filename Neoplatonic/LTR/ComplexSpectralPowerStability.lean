import Neoplatonic.LTR.ComplexSpectralPowerExponentContinuity

/-!
# Lifting scalar spectral-weight estimates to global Hilbert-operator norms

The spectral-power operators are actual bounded diagonal maps on
ℓ²(ℕ,ℂ²). Their difference is exactly the block-diagonal map
with the differences of the real spectral weights. Thus any uniform
scalar estimate yields an operator norm estimate for the entire
infinite-dimensional Dirac Hilbert space, without assumptions on
the edge-coupling sequence.

A sharp bound in the exponent parameters can be supplied by
scalar exponential inequalities in a subsequent theorem.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Global operator difference is the concrete bounded diagonal of
the coordinatewise differences of the scalar spectral weights. -/
theorem chosenComplexSpectralPower_sub_eq_diagonal
    (scale : ℕ → ℝ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (K : ℝ) (hK : 0 ≤ K)
    (hw : ∀ j : ℕ,
      |complexSpectralPowerWeight scale p j -
       complexSpectralPowerWeight scale q j| ≤ K) :
    chosenComplexSpectralPowerCLM scale p hp -
      chosenComplexSpectralPowerCLM scale q hq =
    complexBoundedBlockDiagonal
      (fun j => complexSpectralPowerWeight scale p j -
        complexSpectralPowerWeight scale q j) K hK hw := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  rw [ContinuousLinearMap.sub_apply, lp.coeFn_sub, Pi.sub_apply,
    chosenComplexSpectralPowerCLM_apply,
    chosenComplexSpectralPowerCLM_apply,
    complexBoundedBlockDiagonal_apply]
  simp only [Complex.ofReal_sub, sub_smul]

/-- Any uniform scalar spectral-power weight difference bound lifts
to an operator norm bound on the actual infinite Dirac Hilbert space. -/
theorem chosenComplexSpectralPower_sub_norm_le
    (scale : ℕ → ℝ) (p q : ℝ) (hp : 0 < p) (hq : 0 < q)
    (K : ℝ) (hK : 0 ≤ K)
    (hw : ∀ j : ℕ,
      |complexSpectralPowerWeight scale p j -
       complexSpectralPowerWeight scale q j| ≤ K) :
    ‖chosenComplexSpectralPowerCLM scale p hp -
      chosenComplexSpectralPowerCLM scale q hq‖ ≤ K := by
  rw [chosenComplexSpectralPower_sub_eq_diagonal
    scale p q hp hq K hK hw]
  exact complexBoundedBlockDiagonal_norm_le _ _ _ _

end Neoplatonic.LTR
