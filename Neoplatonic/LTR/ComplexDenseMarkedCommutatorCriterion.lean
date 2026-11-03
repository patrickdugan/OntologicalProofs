import Neoplatonic.LTR.ComplexDenseMarkedMetric

/-!
# Exact complex commutator norm criterion for dense marked metrics

For a countable dense sequence q in any metric space X, assume the
marked edge enumeration covers every ordered pair of distinct values
of q. The reciprocal-distance scale gives the exact equivalence

   ‖[D, π(a)]‖ ≤ 1  iff  a is globally 1-Lipschitz,

for continuous real observables with a finite edge gradient bound.
The left side is the norm of the actual bounded complex Hilbert
commutator extending the unbounded domain expression.

This is the direct bridge from the spectral operator to the
full metric on a potentially uncountable Stone completion space.
-/

namespace Neoplatonic.LTR

/-- For dense countable metric markings, the unit norm ball of the
bounded complex Hilbert commutator equals the global 1-Lipschitz
ball of continuous real observables. -/
theorem complexDenseMarkedCommutator_norm_le_one_iff_lipschitz
    {X : Type*} [MetricSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (left right : ℕ → X)
    (hdistinct : ∀ j, left j ≠ right j)
    (hcover : ∀ m n, q m ≠ q n →
      ∃ j : ℕ, left j = q m ∧ right j = q n)
    (mass : ℕ → ℝ)
    (a : X → ℝ) (ha : Continuous a)
    (L : ℝ) (hL : 0 ≤ L)
    (hEdge : ∀ j,
      |(dist (left j) (right j))⁻¹ *
         (a (right j) - a (left j))| ≤ L) :
    ‖complexPairCommutatorCLM
      mass
      (fun j => (dist (left j) (right j))⁻¹)
      (fun j => a (left j))
      (fun j => a (right j))
      L hL hEdge‖ ≤ 1 ↔
    ∀ x y : X, |a x - a y| ≤ dist x y := by
  exact (complexPairCommutator_norm_le_iff
      mass
      (fun j => (dist (left j) (right j))⁻¹)
      (fun j => a (left j))
      (fun j => a (right j))
      L 1 hL hEdge (by norm_num)).trans
    (denseMarkedEdgeUnitBound_iff_lipschitz
      q hq left right hdistinct hcover a ha)

end Neoplatonic.LTR
