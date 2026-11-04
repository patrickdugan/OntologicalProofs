import Neoplatonic.LTR.MorphospaceGapMonotonicity
import Mathlib

/-!
# MOR-10: delayed information has strictly positive two-step value

Finite rational Bellman inequalities and a closed-form Bernoulli
two-cell plateau witness. This module does not formalize the full
beta-binomial e-process or Python's conservative rational bisection.

All predictive probabilities are planning weights, while the QO-07
statistical coverage proof remains a separate obligation.
-/

namespace Neoplatonic.LTR.Morphospace

/-- With a legal second probe, averaging its two refined gaps never
exceeds the current post-first-observation gap, under nested evidence. -/
theorem two_step_conditional_gain
    (now holdNext hitNext p : ℚ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hh : holdNext ≤ now) (ht : hitNext ≤ now) :
    (1-p)*holdNext+p*hitNext ≤ now := by
  have h := expected_gap_reduction_nonnegative
    now holdNext hitNext p hp0 hp1 hh ht
  linarith

/-- An adaptive second probe can be chosen separately after a hold or
a hit. Every such valid second step has predicted expected gap no
greater than taking the first outcome alone. -/
theorem two_step_recourse_dominates_one
    (p qHold qHit : ℚ)
    (oneHold oneHit : ℚ)
    (twoHoldHold twoHoldHit twoHitHold twoHitHit : ℚ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hqHold0 : 0 ≤ qHold) (hqHold1 : qHold ≤ 1)
    (hqHit0 : 0 ≤ qHit) (hqHit1 : qHit ≤ 1)
    (hHH : twoHoldHold ≤ oneHold)
    (hHT : twoHoldHit ≤ oneHold)
    (hTH : twoHitHold ≤ oneHit)
    (hTT : twoHitHit ≤ oneHit) :
    (1-p)*((1-qHold)*twoHoldHold+qHold*twoHoldHit)
      +p*((1-qHit)*twoHitHold+qHit*twoHitHit)
      ≤ (1-p)*oneHold+p*oneHit := by
  have hHold := two_step_conditional_gain
    oneHold twoHoldHold twoHoldHit qHold
    hqHold0 hqHold1 hHH hHT
  have hHit := two_step_conditional_gain
    oneHit twoHitHold twoHitHit qHit
    hqHit0 hqHit1 hTH hTT
  have hNonneg : 0 ≤ 1-p := sub_nonneg.mpr hp1
  have hWeightedHold :=
    mul_le_mul_of_nonneg_left hHold hNonneg
  have hWeightedHit :=
    mul_le_mul_of_nonneg_left hHit hp0
  linarith

/-- An optimized depth-two value is bounded by the value of any
admissible depth-two policy. In particular it is bounded by the
depth-one value when that first action attains the depth-one optimum
and its two continuation branches satisfy the refinement condition. -/
theorem two_step_optimum_le_one
    (V₂ p qHold qHit oneHold oneHit
     twoHoldHold twoHoldHit twoHitHold twoHitHit : ℚ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hqHold0 : 0 ≤ qHold) (hqHold1 : qHold ≤ 1)
    (hqHit0 : 0 ≤ qHit) (hqHit1 : qHit ≤ 1)
    (hHH : twoHoldHold ≤ oneHold)
    (hHT : twoHoldHit ≤ oneHold)
    (hTH : twoHitHold ≤ oneHit)
    (hTT : twoHitHit ≤ oneHit)
    (hOptimal : V₂ ≤
      (1-p)*((1-qHold)*twoHoldHold+qHold*twoHoldHit)
      +p*((1-qHit)*twoHitHold+qHit*twoHitHit)) :
    V₂ ≤ (1-p)*oneHold+p*oneHit := by
  exact hOptimal.trans
    (two_step_recourse_dominates_one
      p qHold qHit oneHold oneHit
      twoHoldHold twoHoldHit twoHitHold twoHitHit
      hp0 hp1 hqHold0 hqHold1 hqHit0 hqHit1
      hHH hHT hTH hTT)

/-- The uniform-Beta likelihood threshold with two named streams,
one observation and alpha=1/20 is exactly 1/80. -/
theorem two_cell_one_observation_threshold :
    (1 / 20 : ℚ) / (2 * 2) = 1 / 80 := by
  norm_num

/-- A first observation cannot change the gap if another cell still
has the full [0,1] interval. Both possible gaps equal 1/2. -/
theorem two_cell_first_probe_has_zero_gain :
    (1 / 2 : ℚ) -
      ((1 / 2) * (1 / 2) + (1 / 2) * (1 / 2)) = 0 := by
  norm_num

/-- When the two independently sampled cells yield the same bit,
their ideal unrounded intervals both move inward from one endpoint,
and the robust half-range is 79/160. -/
theorem two_cell_equal_bits_gap :
    ((1 : ℚ) - 1 / 80) / 2 = 79 / 160 := by
  norm_num

/-- Under Beta(1,1) planning, two bits agree with probability 1/2.
The exact two-step expected gap falls to 159/320. -/
theorem two_cell_two_step_expected_gap :
    (1 / 2 : ℚ) * (79 / 160) +
      (1 / 2) * (1 / 2) = 159 / 320 := by
  norm_num

/-- Strict two-step gain coexists with zero one-step gain. This is
a model-specific delayed-information witness. -/
theorem two_cell_strict_delayed_value :
    (0 : ℚ) <
      (1 / 2) -
        ((1 / 2) * (79 / 160) + (1 / 2) * (1 / 2)) := by
  norm_num

theorem two_cell_exact_gain :
    (1 / 2 : ℚ) -
      ((1 / 2) * (79 / 160) + (1 / 2) * (1 / 2))
        = 1 / 320 := by
  norm_num

end Neoplatonic.LTR.Morphospace
