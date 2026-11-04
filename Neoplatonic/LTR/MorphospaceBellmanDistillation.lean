import Neoplatonic.LTR.MorphospaceCertificateReachability
import Mathlib

/-!
# MOR-12: decision regret for approximate certificate-Bellman action values

The argument is elementary. If every approximated action value differs
from its true Bellman probability by at most ε, the action chosen by
maximizing the approximation loses at most 2ε in exact Bellman value.

This is a conditional theorem. Neural training, generalization, and
the quality of the approximation are empirical obligations of QO-14.
-/

namespace Neoplatonic.LTR.Morphospace

universe u

/-- A uniform absolute error for estimated action values. -/
def UniformActionValueError {A : Type u}
    (actual estimated : A → ℚ) (ε : ℚ) : Prop :=
  ∀ a, |estimated a - actual a| ≤ ε

/-- Maximizing a uniformly accurate approximate Bellman Q-value
incurs at most 2ε regret in the true per-action certificate
probability. No assumption on the action set's cardinality is
required beyond supplied maximizing witnesses. -/
theorem approximate_bellman_action_regret
    {A : Type u} (actual estimated : A → ℚ)
    (ε : ℚ) (best chosen : A)
    (hApprox : UniformActionValueError actual estimated ε)
    (hBest : ∀ a, actual a ≤ actual best)
    (hChosen : ∀ a, estimated a ≤ estimated chosen) :
    (0 : ℚ) ≤ actual best - actual chosen ∧
      actual best - actual chosen ≤ 2 * ε := by
  have hb := abs_le.mp (hApprox best)
  have hc := abs_le.mp (hApprox chosen)
  have hOrder := hChosen best
  constructor
  · linarith [hBest chosen]
  · linarith

/-- In the two-addressed-cell case a selected predicted maximum
inherits the same quantitative certificate-probability regret bound.
The lean theorem is independent of the student architecture. -/
theorem binary_action_regret
    (true0 true1 pred0 pred1 ε : ℚ)
    (h0 : |pred0 - true0| ≤ ε)
    (h1 : |pred1 - true1| ≤ ε)
    (hChooseZero : pred1 ≤ pred0) :
    true1 - true0 ≤ 2 * ε := by
  have a := (abs_le.mp h0).2
  have b := (abs_le.mp h1).1
  linarith

/-- For an action choice that follows a stable predicted ordering,
a strictly positive true value margin exceeding 2ε guarantees
the correct ordering also holds in the predicted values. -/
theorem robust_action_order_of_margin
    (trueBest trueOther predBest predOther ε : ℚ)
    (hBest : trueOther + 2 * ε < trueBest)
    (hErrBest : |predBest - trueBest| ≤ ε)
    (hErrOther : |predOther - trueOther| ≤ ε) :
    predOther < predBest := by
  have hb := (abs_le.mp hErrBest).1
  have ho := (abs_le.mp hErrOther).2
  linarith

/-- An exact Bellman teacher with zero approximation error gives
zero true regret under any predicted-maximizing action. -/
theorem exact_bellman_student_regret_zero
    {A : Type u} (q : A → ℚ) (best chosen : A)
    (hBest : ∀ a, q a ≤ q best)
    (hChosen : ∀ a, q a ≤ q chosen) :
    q best - q chosen = 0 := by
  have h1 := hBest chosen
  have h2 := hChosen best
  linarith

end Neoplatonic.LTR.Morphospace
