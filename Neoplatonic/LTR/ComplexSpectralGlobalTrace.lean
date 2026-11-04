import Neoplatonic.LTR.ComplexSpectralPowerOperator
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Finite-rank approximants and the global spectral-energy trace

The positive spectral power A_p on H = ℓ²(ℕ, ℂ²) is the
complex-linear diagonal direct sum of w_p(j) I₂. This file constructs
literal finite-rank operators supported on the first N blocks,
identifies their block traces, and proves that their scalar trace
sums converge to the series of all spectral energies for p > 0.

The trace is expressed through the two-dimensional block traces.
An abstract infinite-dimensional trace-class/nuclear-ideal instance
is a separate formalization target; Mathlib v4.35.0 supplies the
finite-dimensional LinearMap.trace used here.
-/

namespace Neoplatonic.LTR

open Filter
open scoped lp Topology

/-- The j-th finite-rank spectral-power operator, supported on
one two-dimensional Hilbert coordinate. -/
noncomputable def complexSingleSpectralPowerBlock
    (scale : ℕ → ℝ) (p : ℝ) (j : ℕ) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  ((lp.singleContinuousLinearMap ℂ
      (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j).comp
        (complexSpectralPowerBlockCLM scale p j)).comp
    (lp.evalCLM ℂ (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j)

/-- Each one-coordinate spectral power has a finite-dimensional range. -/
theorem complexSingleSpectralPowerBlock_compact
    (scale : ℕ → ℝ) (p : ℝ) (j : ℕ) :
    IsCompactOperator (complexSingleSpectralPowerBlock scale p j) := by
  have hev : IsCompactOperator
      (lp.evalCLM ℂ (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  unfold complexSingleSpectralPowerBlock
  exact hev.clm_comp
    ((lp.singleContinuousLinearMap ℂ
      (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j).comp
        (complexSpectralPowerBlockCLM scale p j))

/-- The finite-rank cutoff keeping precisely the first N blocks. -/
noncomputable def finiteComplexSpectralPower
    (scale : ℕ → ℝ) (p : ℝ) (N : ℕ) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  ∑ j ∈ Finset.range N, complexSingleSpectralPowerBlock scale p j

theorem finiteComplexSpectralPower_compact
    (scale : ℕ → ℝ) (p : ℝ) (N : ℕ) :
    IsCompactOperator (finiteComplexSpectralPower scale p N) := by
  classical
  unfold finiteComplexSpectralPower
  induction Finset.range N using Finset.induction_on with
  | empty =>
      simpa using
        (isCompactOperator_zero
          (M₁ := ComplexDiracBlockHilbert) (M₂ := ComplexDiracBlockHilbert))
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact (complexSingleSpectralPowerBlock_compact scale p j).add ih

/-- The actual finite-rank operators agree coordinatewise with
the original global spectral-power operator on the first N blocks. -/
theorem finiteComplexSpectralPower_apply
    (scale : ℕ → ℝ) (p : ℝ) (N : ℕ)
    (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    (finiteComplexSpectralPower scale p N ψ) j =
      if j < N then
        (complexSpectralPowerWeight scale p j : ℂ) • ψ j
      else 0 := by
  classical
  have hsum :
      finiteComplexSpectralPower scale p N ψ =
      ∑ i ∈ Finset.range N,
        lp.single 2 i
          ((complexSpectralPowerWeight scale p i : ℂ) • ψ i) := by
    simp [finiteComplexSpectralPower, complexSingleSpectralPowerBlock,
      complexSpectralPowerBlockCLM, complexScalarBlockCLM,
      lp.evalCLM, lp.evalₗ] <;> rfl
  rw [hsum]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
  simp [Finset.sum_pi_single, Finset.mem_range]

/-- Finite-dimensional trace assembled over the N occupied blocks. -/
noncomputable def finiteComplexSpectralPowerTrace
    (scale : ℕ → ℝ) (p : ℝ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N,
    LinearMap.trace ℂ (EuclideanSpace ℂ (Fin 2))
      (complexSpectralPowerBlockCLM scale p j).toLinearMap

/-- Every finite cutoff trace equals its explicit two-eigenvalue sum. -/
theorem finiteComplexSpectralPowerTrace_eq
    (scale : ℕ → ℝ) (p : ℝ) (N : ℕ) :
    finiteComplexSpectralPowerTrace scale p N =
      ((∑ j ∈ Finset.range N,
        complexSpectralTraceTerm scale p j : ℝ) : ℂ) := by
  simp [finiteComplexSpectralPowerTrace, complexSpectralPowerBlock_trace]

/-- Global spectral-energy trace, defined by the convergent real series. -/
noncomputable def complexSpectralGlobalTrace
    (scale : ℕ → ℝ) (p : ℝ) : ℝ :=
  ∑' j : ℕ, complexSpectralTraceTerm scale p j

/-- The traces of actual finite-rank cutoffs have the expected limit. -/
theorem finiteComplexSpectralPowerTrace_tendsto
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    Tendsto (fun N : ℕ => finiteComplexSpectralPowerTrace scale p N)
      atTop (nhds (complexSpectralGlobalTrace scale p : ℂ)) := by
  have hreal :
      Tendsto (fun N : ℕ =>
        ∑ j ∈ Finset.range N, complexSpectralTraceTerm scale p j)
        atTop (nhds (complexSpectralGlobalTrace scale p)) :=
    (complexSpectralTraceTerm_summable scale p hp).hasSum.tendsto_sum_nat
  have hcomplex := (Complex.continuous_ofReal.tendsto _).comp hreal
  simpa only [Function.comp_def, finiteComplexSpectralPowerTrace_eq] using hcomplex

end Neoplatonic.LTR
