import Neoplatonic.LTR.UnboundedDiracPMap
import Neoplatonic.LTR.DiracBlockCoreDense
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Dense maximal domain for the genuine unbounded Dirac map

The domain consists of Hilbert vectors whose blockwise Dirac images
are themselves square-summable. Every finitely supported Hilbert vector
lies in this domain, since a pointwise finite matrix action preserves
finite support. Finite-block truncations are dense in the full Hilbert
space, and hence the maximal domain is dense.

The result establishes a genuinely *densely defined* partially defined
linear map. It does not assert closedness or equality with its adjoint.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Every finite-block truncation belongs to the maximal domain. -/
theorem finiteBlockTruncation_mem_maximalDiracDomain
    (mass scale : ℕ → ℝ)
    (ψ : DiracBlockHilbert) (s : Finset ℕ) :
    finiteBlockTruncation ψ s ∈ maximalDiracDomain mass scale := by
  change Memℓp (diracBlockwise mass scale (finiteBlockTruncation ψ s)) 2
  apply memℓp_gen
  apply summable_of_ne_finset_zero (s := s)
  intro j hj
  have hz : finiteBlockTruncation ψ s j = 0 :=
    finiteBlockTruncation_apply_of_not_mem ψ s j hj
  have hzero : diracBlockwise mass scale (finiteBlockTruncation ψ s) j = 0 := by
    change euclideanDiracBlock (mass j) (scale j)
      (finiteBlockTruncation ψ s j) = 0
    rw [hz]
    exact (euclideanDiracBlock (mass j) (scale j)).map_zero
  simp [hzero]

/-- The actual maximal domain of the infinite Dirac LinearPMap is dense
in the same infinite Hilbert space in which its image lives. -/
theorem maximalDiracDomain_dense (mass scale : ℕ → ℝ) :
    Dense (maximalDiracDomain mass scale : Set DiracBlockHilbert) := by
  apply Metric.dense_iff.mpr
  intro ψ ε hε
  obtain ⟨s, hs⟩ := finiteBlockTruncation_approx ψ ε hε
  refine ⟨finiteBlockTruncation ψ s, ?_, ?_⟩
  · simpa only [Metric.mem_ball, dist_eq_norm] using hs
  · exact finiteBlockTruncation_mem_maximalDiracDomain mass scale ψ s

end Neoplatonic.LTR
