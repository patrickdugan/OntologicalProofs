import Neoplatonic.LTR.ComplexDiracBlock
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Infinite complex Hilbert Dirac domain and finite-support density

The complex Hilbert space H_C = ℓ²(ℕ, ℂ²) is a genuine infinite
direct sum. The domain of the complex blockwise Dirac operator is
maximal: precisely those vectors whose Dirac block images lie in ℓ².
The operator is complex-linear. Its domain contains every single-block
vector and is dense by finite-block truncations.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Complex Hilbert direct sum of two-component blocks. -/
noncomputable abbrev ComplexDiracBlockHilbert :=
  lp (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2

/-- Blockwise complex-linear action before ℓ² membership is imposed. -/
noncomputable def complexDiracBlockwise (mass scale : ℕ → ℝ)
    (ψ : ComplexDiracBlockHilbert) : ℕ → EuclideanSpace ℂ (Fin 2) :=
  fun j => complexEuclideanDiracBlock (mass j) (scale j) (ψ j)

/-- The exact maximal complex Dirac domain. -/
noncomputable def maximalComplexDiracDomain (mass scale : ℕ → ℝ) :
    Submodule ℂ ComplexDiracBlockHilbert where
  carrier := {ψ | Memℓp (complexDiracBlockwise mass scale ψ) 2}
  zero_mem' := by
    change Memℓp (complexDiracBlockwise mass scale (0 : ComplexDiracBlockHilbert)) 2
    have hz : complexDiracBlockwise mass scale (0 : ComplexDiracBlockHilbert) =
        fun _ => (0 : EuclideanSpace ℂ (Fin 2)) := by
      funext j
      simp [complexDiracBlockwise]
    rw [hz]
    exact zero_mem_ℓp'
  add_mem' := by
    intro x y hx hy
    change Memℓp (complexDiracBlockwise mass scale (x + y)) 2
    have hxy : complexDiracBlockwise mass scale (x + y) =
        complexDiracBlockwise mass scale x + complexDiracBlockwise mass scale y := by
      funext j
      simp only [complexDiracBlockwise, Pi.add_apply, lp.coeFn_add]
      exact (complexEuclideanDiracBlock (mass j) (scale j)).map_add (x j) (y j)
    rw [hxy]
    exact Memℓp.add hx hy
  smul_mem' := by
    intro r x hx
    change Memℓp (complexDiracBlockwise mass scale (r • x)) 2
    have hr : complexDiracBlockwise mass scale (r • x) =
        r • complexDiracBlockwise mass scale x := by
      funext j
      simp only [complexDiracBlockwise, Pi.smul_apply, lp.coeFn_smul]
      exact (complexEuclideanDiracBlock (mass j) (scale j)).map_smul r (x j)
    rw [hr]
    exact Memℓp.const_smul hx r

/-- A genuine partially-defined complex-linear operator on H_C. -/
noncomputable def maximalComplexDiracPMap (mass scale : ℕ → ℝ) :
    ComplexDiracBlockHilbert →ₗ.[ℂ] ComplexDiracBlockHilbert where
  domain := maximalComplexDiracDomain mass scale
  toFun :=
    { toFun := fun ψ =>
        ⟨complexDiracBlockwise mass scale (ψ : ComplexDiracBlockHilbert), ψ.property⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext j
        exact (complexEuclideanDiracBlock (mass j) (scale j)).map_add (x.val j) (y.val j)
      map_smul' := by
        intro r x
        apply lp.ext
        funext j
        exact (complexEuclideanDiracBlock (mass j) (scale j)).map_smul r (x.val j) }

/-- Explicit maximal-domain equation. -/
theorem maximalComplexDiracPMap_domain (mass scale : ℕ → ℝ) :
    (maximalComplexDiracPMap mass scale).domain =
      maximalComplexDiracDomain mass scale := rfl

/-- Finite-block truncation in the complex Hilbert sum. -/
noncomputable def complexFiniteBlockTruncation
    (ψ : ComplexDiracBlockHilbert) (s : Finset ℕ) : ComplexDiracBlockHilbert :=
  ∑ j ∈ s, lp.single 2 j (ψ j)

/-- Truncations vanish outside the chosen finite block set. -/
theorem complexFiniteBlockTruncation_apply_of_not_mem
    (ψ : ComplexDiracBlockHilbert) (s : Finset ℕ)
    (j : ℕ) (hj : j ∉ s) :
    complexFiniteBlockTruncation ψ s j = 0 := by
  simp only [complexFiniteBlockTruncation, lp.coeFn_sum,
    Finset.sum_apply, lp.coeFn_single]
  apply Finset.sum_eq_zero
  intro i hi
  have hij : i ≠ j := by
    intro heq
    exact hj (heq ▸ hi)
  exact Pi.single_eq_of_ne' hij _

/-- Finite-block approximation on the complex Hilbert space. -/
theorem complexFiniteBlockTruncation_approx
    (ψ : ComplexDiracBlockHilbert) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset ℕ, ‖ψ - complexFiniteBlockTruncation ψ s‖ < ε := by
  have hsum :
      HasSum (fun j : ℕ => lp.single 2 j (ψ j)) ψ :=
    lp.hasSum_single (p := (2 : ENNReal)) (by norm_num) ψ
  have hlim : Filter.Tendsto
      (fun s : Finset ℕ => ∑ j ∈ s, lp.single 2 j (ψ j))
      Filter.atTop (nhds ψ) := hsum
  obtain ⟨s, hs⟩ :=
    (hlim.eventually (Metric.ball_mem_nhds ψ hε)).exists
  refine ⟨s, ?_⟩
  have hb : dist (∑ j ∈ s, lp.single 2 j (ψ j)) ψ < ε := by
    simpa only [Metric.mem_ball] using hs
  simpa only [complexFiniteBlockTruncation, dist_eq_norm, norm_sub_rev] using hb

/-- All finite-block truncations belong to the maximal complex domain. -/
theorem complexFiniteBlockTruncation_mem_maximalComplexDiracDomain
    (mass scale : ℕ → ℝ)
    (ψ : ComplexDiracBlockHilbert) (s : Finset ℕ) :
    complexFiniteBlockTruncation ψ s ∈ maximalComplexDiracDomain mass scale := by
  change Memℓp (complexDiracBlockwise mass scale (complexFiniteBlockTruncation ψ s)) 2
  apply memℓp_gen
  apply summable_of_ne_finset_zero (s := s)
  intro j hj
  have hz : complexFiniteBlockTruncation ψ s j = 0 :=
    complexFiniteBlockTruncation_apply_of_not_mem ψ s j hj
  have hzero : complexDiracBlockwise mass scale (complexFiniteBlockTruncation ψ s) j = 0 := by
    change complexEuclideanDiracBlock (mass j) (scale j)
      (complexFiniteBlockTruncation ψ s j) = 0
    rw [hz]
    exact (complexEuclideanDiracBlock (mass j) (scale j)).map_zero
  simp [hzero]

/-- The maximal complex Dirac domain is dense in the full complex Hilbert sum. -/
theorem maximalComplexDiracDomain_dense (mass scale : ℕ → ℝ) :
    Dense (maximalComplexDiracDomain mass scale : Set ComplexDiracBlockHilbert) := by
  apply Metric.dense_iff.mpr
  intro ψ ε hε
  obtain ⟨s, hs⟩ := complexFiniteBlockTruncation_approx ψ ε hε
  refine ⟨complexFiniteBlockTruncation ψ s, ?_, ?_⟩
  · simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hs
  · exact complexFiniteBlockTruncation_mem_maximalComplexDiracDomain mass scale ψ s

end Neoplatonic.LTR
