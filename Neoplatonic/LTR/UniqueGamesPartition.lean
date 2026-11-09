import Mathlib
import Neoplatonic.LTR.UniqueGamesGameSpace

/-!
# UGCS-02: the finite partition function's edge-subset expansion

The identity is purely finite and algebraic: expand a product of
(1 + z * satisfaction-indicator) over the powerset of constraint
occurrences, then exchange the finite world and subset sums.

For F2^s translation games, a separate counting lemma identifies the
inner sum with |K|^(number of connected components of F), provided
every cycle in F has zero holonomy; otherwise the inner sum is zero.
This module does not assert that counting lemma or prove the proposed
thermodynamic phase transition.
-/

namespace Neoplatonic.LTR.UniqueGames.GameSpace

/-- Unnormalized weighted partition function on any finite world space.
    The function f e a can indicate that world a satisfies edge e. -/
def finitePartition {E A : Type*} [Fintype A]
    (edges : Finset E) (f : E → A → ℚ) (z : ℚ) : ℚ :=
  ∑ a : A, ∏ e ∈ edges, (1 + z * f e a)

/-- Exact finite edge-subset expansion, valid for arbitrary rational observables. -/
theorem finitePartition_subset_expansion
    {E A : Type*} [Fintype A] (edges : Finset E)
    (f : E → A → ℚ) (z : ℚ) :
    finitePartition edges f z =
      ∑ t ∈ edges.powerset, z ^ t.card * (∑ a : A, ∏ e ∈ t, f e a) := by
  classical
  unfold finitePartition
  calc
    (∑ a : A, ∏ e ∈ edges, (1 + z * f e a)) =
        ∑ a : A, ∑ t ∈ edges.powerset, ∏ e ∈ t, (z * f e a) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.prod_one_add edges
    _ = ∑ t ∈ edges.powerset, ∑ a : A, ∏ e ∈ t, (z * f e a) := by
      rw [Finset.sum_comm]
    _ = ∑ t ∈ edges.powerset, z ^ t.card * (∑ a : A, ∏ e ∈ t, f e a) := by
      apply Finset.sum_congr rfl
      intro t ht
      simp [Finset.prod_mul_distrib, Finset.prod_const, Finset.mul_sum]

end Neoplatonic.LTR.UniqueGames.GameSpace

#print axioms Neoplatonic.LTR.UniqueGames.GameSpace.finitePartition_subset_expansion
