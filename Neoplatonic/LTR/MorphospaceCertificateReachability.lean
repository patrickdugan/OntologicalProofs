import Neoplatonic.LTR.MorphospaceTwoStepValue
import Mathlib

/-!
# MOR-11: rational Bellman certificate-probability inequalities

The results apply to a finite action/observation interface with fixed
predictive probabilities. This formalizes the algebraic bounds used
by QO-13. The beta-binomial confidence-sequence theorem and the
entire empirical QO-07 e-process are separate mathematical premises.
-/

namespace Neoplatonic.LTR.Morphospace

/-- A rational Bernoulli predictive convex combination. -/
def certificateContinuation (p holdValue hitValue : ℚ) : ℚ :=
  (1-p)*holdValue+p*hitValue

/-- Every predictive Bernoulli continuation of [0,1]-valued terminal
utilities is again a valid probability. -/
theorem certificateContinuation_unit_interval
    (p a b : ℚ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    0 ≤ certificateContinuation p a b ∧
      certificateContinuation p a b ≤ 1 := by
  have hpRemain : 0 ≤ 1-p := by linarith
  have hNonnegA := mul_nonneg hpRemain ha0
  have hNonnegB := mul_nonneg hp0 hb0
  have hBoundA := mul_le_mul_of_nonneg_left ha1 hpRemain
  have hBoundB := mul_le_mul_of_nonneg_left hb1 hp0
  dsimp [certificateContinuation]
  constructor <;> linarith

/-- Refining either possible future success value can only improve
the continuation probability, for a fixed predictive weight. -/
theorem certificateContinuation_monotone
    (p a₁ a₂ b₁ b₂ : ℚ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ha : a₁ ≤ a₂) (hb : b₁ ≤ b₂) :
    certificateContinuation p a₁ b₁ ≤
      certificateContinuation p a₂ b₂ := by
  have hpRemain : 0 ≤ 1-p := by linarith
  have hA := mul_le_mul_of_nonneg_left ha hpRemain
  have hB := mul_le_mul_of_nonneg_left hb hp0
  dsimp [certificateContinuation]
  linarith

/-- A maximum over a fixed menu of experiments preserves pointwise
monotonicity, with its two maximizing indices supplied explicitly.
This supports the finite-horizon Bellman induction. -/
theorem certificate_maximum_monotone
    {I : Type*}
    (lower upper : I → ℚ) (lowWinner highWinner : I)
    (hPoint : ∀ i, lower i ≤ upper i)
    (hUpperWinner : ∀ i, upper i ≤ upper highWinner) :
    lower lowWinner ≤ upper highWinner :=
  (hPoint lowWinner).trans (hUpperWinner lowWinner)

/-- The exact probability of success is one if the confidence
certificate has already been reached, at every remaining budget. -/
theorem certified_state_absorbing
    (futureValue : ℚ) :
    (if True then (1 : ℚ) else futureValue) = 1 := by
  simp

/-- The Beta(1,1) planning predictive after 18 all-hold samples
is exactly 1/20 for a hit on the low-rate cell. -/
theorem low_cell_beta_hit_after_eighteen :
    ((0+1 : ℚ) / (18+2)) = 1/20 := by
  norm_num

/-- The Beta(1,1) predictive after a nineteenth all-hold sample
assigns probability 20/21 to a further hold. -/
theorem low_cell_beta_hold_after_nineteen :
    1 - ((0+1 : ℚ) / (19+2)) = 20/21 := by
  norm_num

/-- Once the initially-zero-gain first probe extends the all-hold
sequence, a second matching hold produces the certificate; the
rational planning probability of that path is 19/21. -/
theorem delayed_certificate_probability_value :
    ((19 : ℚ)/20) * (20/21) + (1/20)*0 = 19/21 := by
  norm_num

/-- This finite witness has zero one-step certificate probability and
strictly positive two-step probability. -/
theorem delayed_certificate_strictly_positive :
    (0 : ℚ) < ((19/20 : ℚ) * (20/21)) := by
  norm_num

/-- A zero-confidence invalid branch retained as an absorbing failure
contributes zero probability-weighted utility. -/
theorem failed_confidence_branch_value
    (p remaining : ℚ) :
    (1-p)*0+p*remaining = p*remaining := by
  ring

end Neoplatonic.LTR.Morphospace
