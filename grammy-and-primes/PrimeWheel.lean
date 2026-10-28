import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.Tactic

/-!
# Factorial-wheel twin-prime candidates

These elementary facts hold for every finite cutoff H, including one
specified by up-arrow notation. They prove local sieve survival and an exact
gap of two, not simultaneous primality. The theorems deliberately avoid
normalizing a gigantic numeral such as Graham's number.
-/

namespace GrammyAndPrimes

/-- A prime divisor of m cannot divide m*k + 1. -/
theorem excludes_plus_one {m k p : ℕ} (hp : Nat.Prime p)
    (hpm : p ∣ m) : ¬ p ∣ m * k + 1 := by
  intro hpair
  have hproduct : p ∣ m * k := dvd_mul_of_dvd_left hpm k
  have hone : p ∣ 1 := (Nat.dvd_add_iff_right hproduct).mpr hpair
  exact hp.not_dvd_one hone

/-- A prime divisor of m cannot divide m*k - 1 when m*k > 0. -/
theorem excludes_minus_one {m k p : ℕ} (hp : Nat.Prime p)
    (hpm : p ∣ m) (hpositive : 0 < m * k) : ¬ p ∣ m * k - 1 := by
  intro hpair
  have hproduct : p ∣ m * k := dvd_mul_of_dvd_left hpm k
  have hcancel : m * k - 1 + 1 = m * k := by omega
  have hsum : p ∣ (m * k - 1) + 1 := by
    rw [hcancel]
    exact hproduct
  have hone : p ∣ 1 := (Nat.dvd_add_iff_right hpair).mpr hsum
  exact hp.not_dvd_one hone

/-- Both factorial-wheel candidates avoid all prime divisors at most H. -/
theorem factorial_pair_sieved (H k p : ℕ) (hk : 0 < k)
    (hp : Nat.Prime p) (hpH : p ≤ H) :
    (¬ p ∣ H.factorial * k - 1) ∧
      (¬ p ∣ H.factorial * k + 1) := by
  have hpm : p ∣ H.factorial := (hp.dvd_factorial).mpr hpH
  have hpositive : 0 < H.factorial * k :=
    Nat.mul_pos (Nat.factorial_pos H) hk
  exact ⟨excludes_minus_one hp hpm hpositive, excludes_plus_one hp hpm⟩

/-- The candidates are exactly two apart, assuming positive k. -/
theorem factorial_pair_gap (H k : ℕ) (hk : 0 < k) :
    H.factorial * k + 1 = (H.factorial * k - 1) + 2 := by
  have hpositive : 0 < H.factorial * k :=
    Nat.mul_pos (Nat.factorial_pos H) hk
  omega

/-- The H = 5 wheel admits a composite/composite pair of gap two. -/
example : (Nat.factorial 5) * 1 - 1 = 119 ∧ (Nat.factorial 5) * 1 + 1 = 121 := by
  decide

end GrammyAndPrimes
