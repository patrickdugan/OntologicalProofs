import Neoplatonic.LTR.MorphospaceBellmanDistillation
import Mathlib

/-!
# MOR-13: two-action regret from the predicted Bellman margin

For a binary QO-13 action menu, the exact per-state action regret of
the greedy QO-15 student is bounded by the absolute error in the
*difference* of the two Q-values. This statewise statement needs no
uniform epsilon bound. A separate triangle bound relates it to the
two individual absolute Q-value errors.

The expectation over any finite held-out distribution follows by
averaging the pointwise inequalities; no distributional or statistical
assumption enters these Lean theorems.
-/

namespace Neoplatonic.LTR.Morphospace

/-- If the predicted Q-value selects action zero, the exact two-action
regret is at most the absolute predicted-margin error. -/
theorem greedy_zero_regret_le_margin_error
    (q0 q1 p0 p1 : ℚ) (hChooseZero : p1 ≤ p0) :
    max q0 q1 - q0 ≤ |(q0 - q1) - (p0 - p1)| := by
  rcases le_total q0 q1 with h01 | h10
  · rw [max_eq_right h01]
    have habs := neg_le_abs ((q0 - q1) - (p0 - p1))
    linarith
  · rw [max_eq_left h10]
    simpa using (abs_nonneg ((q0 - q1) - (p0 - p1)))

/-- The symmetric inequality holds when the predicted Q-value selects
action one. Ties can be assigned consistently to either action. -/
theorem greedy_one_regret_le_margin_error
    (q0 q1 p0 p1 : ℚ) (hChooseOne : p0 ≤ p1) :
    max q0 q1 - q1 ≤ |(q0 - q1) - (p0 - p1)| := by
  rcases le_total q0 q1 with h01 | h10
  · rw [max_eq_right h01]
    simpa using (abs_nonneg ((q0 - q1) - (p0 - p1)))
  · rw [max_eq_left h10]
    have habs := le_abs_self ((q0 - q1) - (p0 - p1))
    linarith

/-- Predicted action-margin error is bounded by the sum of the two
absolute action-value errors, without a uniform epsilon premise. -/
theorem margin_error_le_sum_action_errors
    (q0 q1 p0 p1 : ℚ) :
    |(q0 - q1) - (p0 - p1)| ≤ |q0 - p0| + |q1 - p1| := by
  rw [show (q0 - q1) - (p0 - p1) =
    (q0 - p0) + (p1 - q1) by ring]
  calc
    |(q0 - p0) + (p1 - q1)| ≤ |q0 - p0| + |p1 - q1| :=
      abs_add_le _ _
    _ = |q0 - p0| + |q1 - p1| := by rw [abs_sub_comm p1 q1]

/-- Pointwise empirical regret is thus controlled directly by the
two Q-value errors for a greedy action-zero student. -/
theorem greedy_zero_regret_le_sum_action_errors
    (q0 q1 p0 p1 : ℚ) (hChooseZero : p1 ≤ p0) :
    max q0 q1 - q0 ≤ |q0 - p0| + |q1 - p1| := by
  calc
    max q0 q1 - q0 ≤ |(q0 - q1) - (p0 - p1)| :=
      greedy_zero_regret_le_margin_error q0 q1 p0 p1 hChooseZero
    _ ≤ |q0 - p0| + |q1 - p1| :=
      margin_error_le_sum_action_errors q0 q1 p0 p1

end Neoplatonic.LTR.Morphospace
