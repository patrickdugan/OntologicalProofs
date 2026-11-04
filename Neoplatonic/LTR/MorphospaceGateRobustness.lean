import Neoplatonic.LTR.MorphospaceMarginRegret
import Mathlib

/-!
# MOR-14: confidence for the binary QO-17 engagement gate

A two-output recurrent student engages its learned action selector when
max(p0,p1) ≥ τ, otherwise the original QO-07 bottleneck selector is used.
When both Q predictions have absolute error ≤ ε on the *current* public
state, the max score's error is at most ε. Consequently, a true teacher
score separated from τ by more than ε preserves the engage/fallback
decision. This theorem is conditional and pointwise: QO-17 fitting or
held-out MAE does not establish the premise on new evidence.
-/

namespace Neoplatonic.LTR.Morphospace

/-- Two per-action prediction errors at most ε bound the maximum
prediction error by ε for a binary Bellman action menu. -/
theorem binary_predicted_max_error
    (q0 q1 p0 p1 ε : ℚ)
    (h0 : |p0 - q0| ≤ ε)
    (h1 : |p1 - q1| ≤ ε) :
    |max p0 p1 - max q0 q1| ≤ ε := by
  have h0lo := (abs_le.mp h0).1
  have h0hi := (abs_le.mp h0).2
  have h1lo := (abs_le.mp h1).1
  have h1hi := (abs_le.mp h1).2
  have hpUpper : max p0 p1 ≤ max q0 q1 + ε := by
    apply max_le
    · linarith [le_max_left q0 q1]
    · linarith [le_max_right q0 q1]
  have hqUpper : max q0 q1 ≤ max p0 p1 + ε := by
    apply max_le
    · linarith [le_max_left p0 p1]
    · linarith [le_max_right p0 p1]
  apply abs_le.mpr
  constructor <;> linarith

/-- A true teacher score separated below the gate by ε guarantees
that the student invokes bottleneck fallback. -/
theorem binary_gate_fallback_of_true_margin
    (q0 q1 p0 p1 τ ε : ℚ)
    (h0 : |p0 - q0| ≤ ε)
    (h1 : |p1 - q1| ≤ ε)
    (hFarBelow : max q0 q1 + ε < τ) :
    max p0 p1 < τ := by
  have hMax := (abs_le.mp
    (binary_predicted_max_error q0 q1 p0 p1 ε h0 h1)).2
  linarith

/-- A true teacher progress score exceeding the gate by ε guarantees
that the student remains engaged under the same conditional premise. -/
theorem binary_gate_engagement_of_true_margin
    (q0 q1 p0 p1 τ ε : ℚ)
    (h0 : |p0 - q0| ≤ ε)
    (h1 : |p1 - q1| ≤ ε)
    (hFarAbove : τ + ε < max q0 q1) :
    τ < max p0 p1 := by
  have hMax := (abs_le.mp
    (binary_predicted_max_error q0 q1 p0 p1 ε h0 h1)).1
  linarith

end Neoplatonic.LTR.Morphospace
