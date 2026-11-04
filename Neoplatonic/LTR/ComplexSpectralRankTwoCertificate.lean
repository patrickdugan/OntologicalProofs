import Neoplatonic.LTR.ComplexSpectralNuclearSeries

/-!
# Explicit summable rank-two factorization certificate

A certificate consists of a norm-summable series of operators
factoring through ℂ² whose Hilbert-space operator sum is the
target. Since every factor has rank at most two, each trace norm
is bounded by twice its operator norm. Thus this is a concrete
nuclear / trace-class criterion for the specified Hilbert operator.

It is intentionally independent of a general Schatten ideal API,
which is absent from the pinned Mathlib v4.35.0.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- A genuine rank-at-most-two norm-nuclear expansion,
with factorization and equality of continuous linear maps. -/
def HasSummableRankTwoExpansion
    (A : ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert) : Prop :=
  ∃ B : ℕ → (ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert),
    (∀ j, ∃ U : ComplexDiracBlockHilbert →L[ℂ] EuclideanSpace ℂ (Fin 2),
      ∃ V : EuclideanSpace ℂ (Fin 2) →L[ℂ] ComplexDiracBlockHilbert,
        B j = V.comp U) ∧
    Summable (fun j => ‖B j‖) ∧
    HasSum B A

/-- Every concrete spectral power at p>0 carries an explicit
summable rank-two decomposition of the whole infinite Hilbert operator. -/
theorem chosenComplexSpectralPower_rankTwoCertificate
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    HasSummableRankTwoExpansion
      (chosenComplexSpectralPowerCLM scale p hp) := by
  refine ⟨complexSingleSpectralPowerBlock scale p, ?_,
    complexSingleSpectralPowerBlock_norm_summable scale p hp, ?_⟩
  · intro j
    refine ⟨lp.evalCLM ℂ
      (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j,
      (lp.singleContinuousLinearMap ℂ
        (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j).comp
          (complexSpectralPowerBlockCLM scale p j), ?_⟩
    rfl
  · rw [chosenComplexSpectralPower_eq_tsum_rankTwo scale p hp]
    exact (complexSingleSpectralPowerBlock_summable scale p hp).hasSum

end Neoplatonic.LTR
