import Neoplatonic.LTR.ComplexSpectralBasisTrace
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval

/-!
# Nuclear decomposition of the concrete complex spectral power

For p > 0 the genuine infinite Hilbert-space operator A_p is the
operator-norm sum of its rank-at-most-two blocks.  The sum of their
operator norms is bounded by the scalar spectral-energy series.

This is a concrete finite-rank nuclear decomposition, with a checked
operator equality; the next module will refine it to rank-one terms.
A general-purpose Schatten trace ideal is not assumed.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Every individual rank-two cutoff block has operator norm bounded
by its positive scalar spectral-power coefficient. -/
theorem complexSingleSpectralPowerBlock_norm_le
    (scale : ℕ → ℝ) (p : ℝ) (j : ℕ) :
    ‖complexSingleSpectralPowerBlock scale p j‖ ≤
      complexSpectralPowerWeight scale p j := by
  have hw := complexSpectralPowerWeight_nonneg scale p j
  have hb : ‖complexSpectralPowerBlockCLM scale p j‖ ≤
      complexSpectralPowerWeight scale p j := by
    change ‖complexScalarBlockCLM (complexSpectralPowerWeight scale p j)‖ ≤ _
    simpa only [abs_of_nonneg hw] using
      (complexScalarBlockCLM_norm_le
        (complexSpectralPowerWeight scale p j))
  apply ContinuousLinearMap.opNorm_le_bound _ hw
  intro ψ
  change ‖lp.single 2 j
    (complexSpectralPowerBlockCLM scale p j (ψ j))‖ ≤
      complexSpectralPowerWeight scale p j * ‖ψ‖
  rw [lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2) j]
  calc
    ‖complexSpectralPowerBlockCLM scale p j (ψ j)‖ ≤
      ‖complexSpectralPowerBlockCLM scale p j‖ * ‖ψ j‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ complexSpectralPowerWeight scale p j * ‖ψ j‖ :=
        mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ ≤ complexSpectralPowerWeight scale p j * ‖ψ‖ :=
        mul_le_mul_of_nonneg_left
          (lp.norm_apply_le_norm
            (by norm_num : (2 : ℝ≥0∞) ≠ 0) ψ j) hw

/-- Every positive exponent gives an absolutely summable family
of actual finite-rank Hilbert operators. -/
theorem complexSingleSpectralPowerBlock_summable
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    Summable (complexSingleSpectralPowerBlock scale p) := by
  have hp2 : 0 < p / 2 := by linarith
  have hs : Summable (complexSpectralPowerWeight scale p) := by
    change Summable (fun j : ℕ =>
      (chosenSquaredResolventWeight scale j) ^ (p / 2))
    exact chosenSquaredResolventWeight_rpow_summable scale (p / 2) hp2
  exact hs.of_norm_bounded
    (fun j => complexSingleSpectralPowerBlock_norm_le scale p j)

/-- The series is absolutely convergent even in operator norm. -/
theorem complexSingleSpectralPowerBlock_norm_summable
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    Summable (fun j => ‖complexSingleSpectralPowerBlock scale p j‖) := by
  have hp2 : 0 < p / 2 := by linarith
  have hs : Summable (complexSpectralPowerWeight scale p) := by
    change Summable (fun j : ℕ =>
      (chosenSquaredResolventWeight scale j) ^ (p / 2))
    exact chosenSquaredResolventWeight_rpow_summable scale (p / 2) hp2
  exact Summable.of_nonneg_of_le (fun j => norm_nonneg _)
    (fun j => complexSingleSpectralPowerBlock_norm_le scale p j) hs

/-- The actual full Hilbert operator, when applied to a vector,
is the sum of all its coordinate-supported rank-two blocks. -/
theorem complexSingleSpectralPowerBlock_hasSum_apply
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p)
    (ψ : ComplexDiracBlockHilbert) :
    HasSum (fun j => complexSingleSpectralPowerBlock scale p j ψ)
      (chosenComplexSpectralPowerCLM scale p hp ψ) := by
  convert (lp.hasSum_single
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
      (chosenComplexSpectralPowerCLM scale p hp ψ)) using 1
  ext j
  simp [complexSingleSpectralPowerBlock,
    complexSpectralPowerBlockCLM, complexScalarBlockCLM,
    chosenComplexSpectralPowerCLM_apply, lp.evalCLM, lp.evalₗ]

/-- Operator-norm nuclear series identity for the actual spectral power. -/
theorem chosenComplexSpectralPower_eq_tsum_rankTwo
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    chosenComplexSpectralPowerCLM scale p hp =
      ∑' j : ℕ, complexSingleSpectralPowerBlock scale p j := by
  apply ContinuousLinearMap.ext
  intro ψ
  have hsum := (complexSingleSpectralPowerBlock_summable scale p hp).hasSum
  have hmap : HasSum
      (fun j => complexSingleSpectralPowerBlock scale p j ψ)
      ((∑' j : ℕ, complexSingleSpectralPowerBlock scale p j) ψ) :=
    hsum.hasSum_apply ψ
  exact (hmap.unique
    (complexSingleSpectralPowerBlock_hasSum_apply scale p hp ψ)).symm

end Neoplatonic.LTR
