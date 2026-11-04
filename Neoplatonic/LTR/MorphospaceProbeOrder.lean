import Neoplatonic.LTR.MorphospaceCertificateReachability
import Mathlib

/-!
# MOR-12: independent probe order can erase first-action supervision

Given two independent Bernoulli streams and a terminal utility indexed
only by each stream's own hit/hold outcome, the expected utility of
probing A then B equals B then A if each stream is sampled exactly
once and there is no action cost, intermediate decision, or
state-changing intervention coupling the streams.

This does not assert equality for a full QO-13 adaptive Bellman policy:
that policy may sample the SAME cell twice, choose a second cell in
response to the first outcome, or have different action costs.
The theorem captures the simple order-indifferent subproblem behind
QO-14's sparse non-tied exact Q-value labels.
-/

namespace Neoplatonic.LTR.Morphospace

/-- The terminal utilities are indexed by A's outcome (first bit)
and B's outcome (second bit), regardless of temporal order. -/
def expectedProbeAThenB
    (p q reward00 reward01 reward10 reward11 : ℚ) : ℚ :=
  (1-p)*(1-q)*reward00 +
  (1-p)*q*reward01 +
  p*(1-q)*reward10 +
  p*q*reward11

/-- Probe B first, A second; each terminal reward keeps its
independently labelled A/B outcome identity. -/
def expectedProbeBThenA
    (p q reward00 reward01 reward10 reward11 : ℚ) : ℚ :=
  (1-q)*(1-p)*reward00 +
  q*(1-p)*reward01 +
  (1-q)*p*reward10 +
  q*p*reward11

/-- Independent Bernoulli observations commute in expected terminal
reward when the joint event is the same under both sampling orders. -/
theorem two_independent_probes_commute
    (p q reward00 reward01 reward10 reward11 : ℚ) :
    expectedProbeAThenB p q reward00 reward01 reward10 reward11 =
      expectedProbeBThenA p q reward00 reward01 reward10 reward11 := by
  dsimp [expectedProbeAThenB, expectedProbeBThenA]
  ring

/-- The equality holds also for binary certificate indicators:
the Boolean reward values are mapped to rational 0 and 1. -/
theorem two_probe_certificate_order_indifferent
    (p q : ℚ) (cert00 cert01 cert10 cert11 : Bool) :
    expectedProbeAThenB p q
      (if cert00 then 1 else 0)
      (if cert01 then 1 else 0)
      (if cert10 then 1 else 0)
      (if cert11 then 1 else 0) =
    expectedProbeBThenA p q
      (if cert00 then 1 else 0)
      (if cert01 then 1 else 0)
      (if cert10 then 1 else 0)
      (if cert11 then 1 else 0) := by
  exact two_independent_probes_commute p q
    (if cert00 then 1 else 0)
    (if cert01 then 1 else 0)
    (if cert10 then 1 else 0)
    (if cert11 then 1 else 0)

/-- If the action alternatives are precisely the two temporal
orderings of one probe from each cell, their optimal first-action
value difference is zero. -/
theorem one_each_two_probe_action_regret_zero
    (p q r00 r01 r10 r11 : ℚ) :
    expectedProbeAThenB p q r00 r01 r10 r11 -
      expectedProbeBThenA p q r00 r01 r10 r11 = 0 := by
  rw [two_independent_probes_commute]
  ring

end Neoplatonic.LTR.Morphospace
