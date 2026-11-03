import Neoplatonic.LTR.ComplexMarkedMetric
import Neoplatonic.LTR.ComplexObservableSeminorm

/-!
# Marked metric Lipschitz condition from the actual bounded commutator

In a metric space with a countable marked enumeration covering all
ordered distinct pairs, take s_j = dist(left_j,right_j)⁻¹.
The verified infinite-Hilbert commutator norm is ≤ 1 exactly when
the represented real function is 1-Lipschitz on the metric space.

This theorem uses the actual bounded continuous linear commutator
rather than replacing it with a purely numerical edge seminorm.
The assertion is conditional on a uniform edge bound, which is what
makes the global commutator a bounded operator in the first place.

The all-pairs enumeration hypothesis must later be replaced by
a dense countable marking for uncountable Stone spaces.
-/

namespace Neoplatonic.LTR

/-- The norm bound on a genuine infinite Hilbert commutator equals the
full metric 1-Lipschitz condition when all distinct pairs are marked. -/
theorem complexMarkedCommutator_norm_le_one_iff_lipschitz
    {X : Type*} [MetricSpace X]
    (left right : ℕ → X)
    (hdistinct : ∀ j, left j ≠ right j)
    (hcover : ∀ x y : X, x ≠ y →
      ∃ j : ℕ, left j = x ∧ right j = y)
    (mass : ℕ → ℝ)
    (a : X → ℝ)
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
    (markedEdgeUnitBound_iff_lipschitz
      left right hdistinct hcover a)

end Neoplatonic.LTR
