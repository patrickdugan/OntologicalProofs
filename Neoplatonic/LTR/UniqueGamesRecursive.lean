import Mathlib

/-!
# LTR-UG-02: exact small-field latent-gadget recurrences

These theorems certify rational recurrences. The interpretation as optimal
full-linear-lift detection for the q=2 fixed tree is a separate written
factorization proof with exhaustive finite kernels in Compactification-Theory.
No arbitrary-alphabet Unique Games reduction is asserted here.
-/

namespace Neoplatonic.LTR.UniqueGames.Recursive

/-- Nonlinear output-change law for the specified q=2 recursion. -/
def noise (n : ℕ) : ℚ := (7 / 8) * (6 / 7) ^ n

def rankOne : ℕ → ℚ
  | 0 => 1 / 2
  | n + 1 => (6 / 7) * rankOne n

def rankTwo : ℕ → ℚ
  | 0 => 3 / 4
  | n + 1 => (4 / 7) * rankTwo n + (3 / 7) * rankOne n

def rankThree : ℕ → ℚ
  | 0 => 7 / 8
  | n + 1 => (1 / 7) * rankThree n + (6 / 7) * rankTwo n

theorem rankOne_closed (n : ℕ) :
    rankOne n = (1 / 2 : ℚ) * (6 / 7) ^ n := by
  induction n with
  | zero => norm_num [rankOne]
  | succ n ih =>
      simp only [rankOne, ih, pow_succ]
      ring

theorem rankTwo_closed (n : ℕ) :
    rankTwo n = (3 / 4 : ℚ) * (6 / 7) ^ n := by
  induction n with
  | zero => norm_num [rankTwo]
  | succ n ih =>
      simp only [rankTwo, ih, rankOne_closed, pow_succ]
      ring

theorem rankThree_closed (n : ℕ) :
    rankThree n = (9 / 10 : ℚ) * (6 / 7) ^ n -
      (1 / 40 : ℚ) * (1 / 7) ^ n := by
  induction n with
  | zero => norm_num [rankThree]
  | succ n ih =>
      simp only [rankThree, ih, rankTwo_closed, pow_succ]
      ring

theorem separation_identity (n : ℕ) :
    rankThree n - noise n =
      (1 / 40 : ℚ) * ((6 / 7) ^ n - (1 / 7) ^ n) := by
  rw [rankThree_closed, noise]
  ring

/-- An all-depth ceiling; it does not assert constant surviving detection. -/
theorem relative_ceiling (n : ℕ) :
    rankThree n < (36 / 35 : ℚ) * noise n := by
  rw [rankThree_closed, noise]
  have hp : (0 : ℚ) < (1 / 7 : ℚ) ^ n := by positivity
  nlinarith

theorem depth_one_future_information_gap :
    rankThree 1 - (3 / 4 : ℚ) = 1 / 56 := by
  norm_num [rankThree, rankTwo]

theorem depth_nine_below_quarter : rankThree 9 < (1 / 4 : ℚ) := by
  rw [rankThree_closed]
  norm_num

/-- Conditional final arithmetic of a harmonic-potential survival proof.
The probability model and expected-drop premise must be supplied separately. -/
theorem harmonic_detection_bound
    (H totalDrop survival detection : ℝ)
    (hH : 0 < H)
    (hExtinction : H * (1 - survival) ≤ totalDrop)
    (hBudget : totalDrop ≤ H / 2)
    (hDetection : survival / 2 ≤ detection) :
    (1 / 4 : ℝ) ≤ detection := by
  have hs : (1 / 2 : ℝ) ≤ survival := by nlinarith
  linarith

end Neoplatonic.LTR.UniqueGames.Recursive

#print axioms Neoplatonic.LTR.UniqueGames.Recursive.rankOne_closed
#print axioms Neoplatonic.LTR.UniqueGames.Recursive.rankTwo_closed
#print axioms Neoplatonic.LTR.UniqueGames.Recursive.rankThree_closed
#print axioms Neoplatonic.LTR.UniqueGames.Recursive.separation_identity
#print axioms Neoplatonic.LTR.UniqueGames.Recursive.relative_ceiling
#print axioms Neoplatonic.LTR.UniqueGames.Recursive.depth_one_future_information_gap
#print axioms Neoplatonic.LTR.UniqueGames.Recursive.depth_nine_below_quarter
#print axioms Neoplatonic.LTR.UniqueGames.Recursive.harmonic_detection_bound
