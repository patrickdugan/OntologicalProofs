import Neoplatonic.LTR.ComplexSpectralCFCDyadicRational
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Local uniform spectral-power bounds in the exponent

For every p₀ > 0, the entire family of actual rank-two Hilbert
spectral-power blocks is dominated by a single summable series
whenever p ≥ p₀/2. These are the Weierstrass M-test hypotheses
for continuity of the global spectral-power operator in p.

The endpoint p = 0 requires a different topology; the
positive-exponent estimate is intentionally bounded away from zero.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Each scalar spectral weight varies continuously in its real exponent. -/
theorem complexSpectralPowerWeight_continuous
    (scale : ℕ → ℝ) (j : ℕ) :
    Continuous (fun p : ℝ => complexSpectralPowerWeight scale p j) := by
  unfold complexSpectralPowerWeight
  have hpos : chosenSquaredResolventWeight scale j ≠ 0 :=
    (chosenSquaredResolventWeight_pos scale j).ne'
  have hdiv : Continuous (fun p : ℝ => p / 2) := by fun_prop
  exact (Real.continuous_const_rpow hpos).comp hdiv

/-- Uniform scalar domination on the positive half-neighborhood
p ≥ p₀/2, regardless of the arbitrary real Dirac edge couplings. -/
theorem complexSpectralPowerWeight_local_majorant
    (scale : ℕ → ℝ) (p₀ : ℝ) (hp₀ : 0 < p₀)
    (p : ℝ) (hp : p₀ / 2 ≤ p) (j : ℕ) :
    complexSpectralPowerWeight scale p j ≤
      (chosenSquaredResolventWeight scale j) ^ (p₀ / 4) := by
  unfold complexSpectralPowerWeight
  have he : p₀ / 4 ≤ p / 2 := by linarith
  exact (Real.antitone_rpow_of_base_le_one
    (chosenSquaredResolventWeight_pos scale j)
    (chosenSquaredResolventWeight_le_one scale j)) he

/-- The dominating spectral energy is summable. -/
theorem complexSpectralPowerWeight_local_majorant_summable
    (scale : ℕ → ℝ) (p₀ : ℝ) (hp₀ : 0 < p₀) :
    Summable (fun j : ℕ =>
      (chosenSquaredResolventWeight scale j) ^ (p₀ / 4)) :=
  chosenSquaredResolventWeight_rpow_summable scale (p₀ / 4) (by linarith)

/-- Actual rank-two Hilbert operator series converge uniformly in
operator norm on the entire exponent half-line p ≥ p₀/2.
This is stronger than pointwise operator convergence for each p. -/
theorem complexSpectralRankTwo_hasSumUniformlyOn
    (scale : ℕ → ℝ) (p₀ : ℝ) (hp₀ : 0 < p₀) :
    HasSumUniformlyOn
      (fun j (p : ℝ) => complexSingleSpectralPowerBlock scale p j)
      (fun p : ℝ => ∑' j : ℕ, complexSingleSpectralPowerBlock scale p j)
      (Set.Ici (p₀ / 2)) := by
  apply HasSumUniformlyOn.of_norm_le_summable
    (complexSpectralPowerWeight_local_majorant_summable scale p₀ hp₀)
  intro j p hp
  exact (complexSingleSpectralPowerBlock_norm_le scale p j).trans
    (complexSpectralPowerWeight_local_majorant scale p₀ hp₀ p hp j)


/-- The unweighted projection onto one two-dimensional Hilbert block. -/
noncomputable def complexSpectralUnitCoordinateCLM (j : ℕ) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  (lp.singleContinuousLinearMap ℂ
    (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j).comp
    (lp.evalCLM ℂ
      (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j)

/-- The spectral block is a continuously varying scalar multiple
of a fixed rank-two Hilbert operator. -/
theorem complexSingleSpectralPowerBlock_eq_weight_smul
    (scale : ℕ → ℝ) (p : ℝ) (j : ℕ) :
    complexSingleSpectralPowerBlock scale p j =
      (complexSpectralPowerWeight scale p j : ℂ) •
        complexSpectralUnitCoordinateCLM j := by
  apply ContinuousLinearMap.ext
  intro ψ
  change lp.single
      (E := fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j
      ((complexSpectralPowerWeight scale p j : ℂ) • ψ j) =
    (complexSpectralPowerWeight scale p j : ℂ) •
      lp.single (E := fun _ : ℕ => EuclideanSpace ℂ (Fin 2))
        2 j (ψ j)
  exact lp.single_smul
    (E := fun _ : ℕ => EuclideanSpace ℂ (Fin 2))
    2 j (complexSpectralPowerWeight scale p j : ℂ) (ψ j)

/-- Each finite-rank Hilbert term is operator-norm continuous in p. -/
theorem complexSingleSpectralPowerBlock_continuous
    (scale : ℕ → ℝ) (j : ℕ) :
    Continuous (fun p : ℝ => complexSingleSpectralPowerBlock scale p j) := by
  have hw : Continuous (fun p : ℝ =>
      (complexSpectralPowerWeight scale p j : ℂ)) :=
    Complex.continuous_ofReal.comp
      (complexSpectralPowerWeight_continuous scale j)
  have hfun :
      (fun p : ℝ => complexSingleSpectralPowerBlock scale p j) =
      (fun p : ℝ =>
        (complexSpectralPowerWeight scale p j : ℂ) •
          complexSpectralUnitCoordinateCLM j) := by
    funext p
    exact complexSingleSpectralPowerBlock_eq_weight_smul scale p j
  rw [hfun]
  exact hw.smul continuous_const

/-- Each finite sum of spectral-power Hilbert blocks is continuous
in the exponent, with no positivity restriction. -/
theorem finiteComplexSpectralPower_continuous_exponent
    (scale : ℕ → ℝ) (s : Finset ℕ) :
    Continuous (fun p : ℝ =>
      ∑ j ∈ s, complexSingleSpectralPowerBlock scale p j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        (continuous_const : Continuous (fun _ : ℝ =>
          (0 : ComplexDiracBlockHilbert →L[ℂ]
            ComplexDiracBlockHilbert)))
  | @insert j s hj ih =>
      have hstep :=
        (complexSingleSpectralPowerBlock_continuous scale j).add ih
      have heq :
          (fun p : ℝ =>
            ∑ i ∈ Finset.insert j s,
              complexSingleSpectralPowerBlock scale p i) =
          ((fun p : ℝ => complexSingleSpectralPowerBlock scale p j) +
            fun p : ℝ => ∑ i ∈ s,
              complexSingleSpectralPowerBlock scale p i) := by
        funext p
        simp [Finset.sum_insert hj, Pi.add_apply]
      rw [heq]
      exact hstep

/-- The complete operator-norm block series is continuous in the
positive real exponent on every closed half-line away from zero. -/
theorem complexSpectralPowerSeries_continuousOn_positive
    (scale : ℕ → ℝ) (p₀ : ℝ) (hp₀ : 0 < p₀) :
    ContinuousOn (fun p : ℝ =>
      ∑' j : ℕ, complexSingleSpectralPowerBlock scale p j)
      (Set.Ici (p₀ / 2)) := by
  have hu :=
    (complexSpectralRankTwo_hasSumUniformlyOn scale p₀ hp₀).tendstoUniformlyOn
  apply hu.continuousOn
  have hc : ∀ s : Finset ℕ,
      ContinuousOn (fun p : ℝ =>
        ∑ j ∈ s, complexSingleSpectralPowerBlock scale p j)
        (Set.Ici (p₀ / 2)) :=
    fun s => (finiteComplexSpectralPower_continuous_exponent scale s).continuousOn
  exact (Filter.Eventually.of_forall hc).frequently


end Neoplatonic.LTR
