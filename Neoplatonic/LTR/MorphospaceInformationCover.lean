import Neoplatonic.LTR.MorphospaceAnytimeIntervals
import Mathlib

/-!
# MOR-08: exact finite rational fractional-cover primal/dual certificate

For a finite alternative-by-probe incidence matrix A, let a
nonnegative expected-query allocation x cover every alternative.
Let a nonnegative alternative weighting y pack into the per-cell
probe costs w. Weak duality bounds the total probe cost below by
the sum of alternative weights.

This is ordinary linear-programming weak duality, formalized as a
small mathematical component of EvalMath QI-03. Its theorem says
nothing about how an adaptive policy acquires its information:
the KL/data-processing premise belongs to EvalMath QI-02/QI-03.
-/

namespace Neoplatonic.LTR.Morphospace

/-- Every feasible dual weighting gives a certified lower bound on the
cost of every feasible fractional probe allocation. No assumption on
the signs of incidence coefficients is needed in this algebraic step. -/
theorem fractional_information_cover_weak_duality
    {m n : ℕ}
    (A : Fin m → Fin n → ℚ)
    (w : Fin n → ℚ)
    (x : Fin n → ℚ)
    (y : Fin m → ℚ)
    (hx : ∀ i, 0 ≤ x i)
    (hy : ∀ j, 0 ≤ y j)
    (hcover : ∀ j, (1 : ℚ) ≤ ∑ i, A j i * x i)
    (hdual : ∀ i, (∑ j, A j i * y j) ≤ w i) :
    (∑ j, y j) ≤ ∑ i, w i * x i := by
  calc
    (∑ j, y j) = ∑ j, (1 : ℚ) * y j := by simp
    _ ≤ ∑ j, (∑ i, A j i * x i) * y j := by
      apply Finset.sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_right (hcover j) (hy j)
    _ = ∑ i, (∑ j, A j i * y j) * x i := by
      calc
        (∑ j, (∑ i, A j i * x i) * y j) =
            ∑ j, ∑ i, (A j i * x i) * y j := by
          simp_rw [Finset.sum_mul]
        _ = ∑ i, ∑ j, (A j i * x i) * y j := by
          rw [Finset.sum_comm]
        _ = ∑ i, ∑ j, (A j i * y j) * x i := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = ∑ i, (∑ j, A j i * y j) * x i := by
          simp_rw [Finset.sum_mul]
    _ ≤ ∑ i, w i * x i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hdual i) (hx i)

/-- If a primal feasible allocation and a dual feasible weighting have
equal objectives, the primal is globally minimum-cost among ALL
feasible allocations. This is a source-independent optimality witness. -/
theorem fractional_information_equal_objectives_optimal
    {m n : ℕ}
    (A : Fin m → Fin n → ℚ)
    (w : Fin n → ℚ)
    (x : Fin n → ℚ)
    (y : Fin m → ℚ)
    (hy : ∀ j, 0 ≤ y j)
    (hdual : ∀ i, (∑ j, A j i * y j) ≤ w i)
    (heq : (∑ i, w i * x i) = ∑ j, y j)
    (x' : Fin n → ℚ)
    (hx' : ∀ i, 0 ≤ x' i)
    (hcover' : ∀ j, (1 : ℚ) ≤ ∑ i, A j i * x' i) :
    (∑ i, w i * x i) ≤ ∑ i, w i * x' i := by
  calc
    (∑ i, w i * x i) = ∑ j, y j := heq
    _ ≤ ∑ i, w i * x' i :=
      fractional_information_cover_weak_duality
        A w x' y hx' hy hcover' hdual

/-- The dual formulation is meaningful even without constructing a
candidate primal optimum: any nonnegative alternative weighting that
respects cell capacities is a universal lower-bound witness. -/
theorem fractional_information_dual_certificate
    {m n : ℕ}
    (A : Fin m → Fin n → ℚ)
    (w : Fin n → ℚ)
    (y : Fin m → ℚ)
    (hy : ∀ j, 0 ≤ y j)
    (hdual : ∀ i, (∑ j, A j i * y j) ≤ w i)
    (x : Fin n → ℚ)
    (hx : ∀ i, 0 ≤ x i)
    (hcover : ∀ j, (1 : ℚ) ≤ ∑ i, A j i * x i) :
    (∑ j, y j) ≤ ∑ i, w i * x i :=
  fractional_information_cover_weak_duality
    A w x y hx hy hcover hdual

end Neoplatonic.LTR.Morphospace
