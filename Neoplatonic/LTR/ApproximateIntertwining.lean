import Mathlib

/-!
# Quantitative transport through repeated linear steps

The one-step defect is `B * L - L * A`.  A telescoping identity gives its
contribution after any finite number of steps.  The norm estimates use a
submultiplicative norm with `‖1‖ = 1`, as provided by operator algebras on
nontrivial normed spaces.  An entrywise matrix norm must be checked separately
before these estimates are applied to it.

These are conditional estimates for fixed linear operators.  Applying them to
a neural model requires a justified operator model and bounds on its defect.
-/

namespace Neoplatonic.LTR.ApproximateIntertwining

open Finset

section Algebra

variable {R : Type*} [Ring R]

/-- The defect at the next step splits into the old defect and one new term. -/
theorem power_defect_succ (A B L : R) (n : ℕ) :
    B ^ (n + 1) * L - L * A ^ (n + 1) =
      (B ^ n * L - L * A ^ n) * A + B ^ n * (B * L - L * A) := by
  rw [pow_succ, pow_succ]
  noncomm_ring

/-- The exact finite defect expansion, with the order of multiplication retained. -/
theorem power_defect_sum (A B L : R) (n : ℕ) :
    B ^ n * L - L * A ^ n =
      ∑ j ∈ range n, B ^ j * (B * L - L * A) * A ^ (n - 1 - j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsum :
          (∑ j ∈ range n, B ^ j * (B * L - L * A) * A ^ (n - 1 - j)) * A =
            ∑ j ∈ range n, B ^ j * (B * L - L * A) * A ^ (n - j) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j hj
        have hjn := Finset.mem_range.mp hj
        have hexp : n - 1 - j + 1 = n - j := by omega
        rw [mul_assoc, ← pow_succ, hexp]
      rw [power_defect_succ, ih, hsum, Finset.sum_range_succ]
      simp

/-- Exact transport is recovered when the one-step defect vanishes. -/
theorem powers_intertwine (A B L : R) (h : B * L = L * A) (n : ℕ) :
    B ^ n * L = L * A ^ n := by
  apply sub_eq_zero.mp
  rw [power_defect_sum]
  simp [h]

end Algebra

section NormEstimates

variable {R : Type*} [NormedRing R] [NormOneClass R]

/-- Separate bounds for each operator give a finite scalar convolution. -/
theorem norm_power_defect_le (A B L : R) (n : ℕ) {α β ε : ℝ}
    (hA : ‖A‖ ≤ α) (hB : ‖B‖ ≤ β) (hE : ‖B * L - L * A‖ ≤ ε) :
    ‖B ^ n * L - L * A ^ n‖ ≤
      ∑ j ∈ range n, β ^ j * ε * α ^ (n - 1 - j) := by
  rw [power_defect_sum]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro j hj
  have hApow : ‖A ^ (n - 1 - j)‖ ≤ α ^ (n - 1 - j) :=
    (norm_pow_le A _).trans (pow_le_pow_left₀ (norm_nonneg A) hA _)
  have hBpow : ‖B ^ j‖ ≤ β ^ j :=
    (norm_pow_le B _).trans (pow_le_pow_left₀ (norm_nonneg B) hB _)
  exact norm_mul_le_of_le (norm_mul_le_of_le hBpow hE) hApow

/-- A common operator bound yields the explicit rate `(n+1) ρ^n ε`. -/
theorem norm_power_defect_succ_le (A B L : R) (n : ℕ) {ρ ε : ℝ}
    (hA : ‖A‖ ≤ ρ) (hB : ‖B‖ ≤ ρ) (hE : ‖B * L - L * A‖ ≤ ε) :
    ‖B ^ (n + 1) * L - L * A ^ (n + 1)‖ ≤
      (n + 1 : ℕ) * ρ ^ n * ε := by
  calc
    ‖B ^ (n + 1) * L - L * A ^ (n + 1)‖ ≤
        ∑ j ∈ range (n + 1), ρ ^ j * ε * ρ ^ (n + 1 - 1 - j) :=
      norm_power_defect_le A B L (n + 1) hA hB hE
    _ = ∑ _j ∈ range (n + 1), ρ ^ n * ε := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjn : j ≤ n := by simpa using Finset.mem_range.mp hj
      calc
        ρ ^ j * ε * ρ ^ (n + 1 - 1 - j) =
            (ρ ^ j * ρ ^ (n - j)) * ε := by simp only [Nat.add_sub_cancel]; ring
        _ = ρ ^ n * ε := by rw [← pow_add, Nat.add_sub_of_le hjn]
    _ = (n + 1 : ℕ) * ρ ^ n * ε := by simp [nsmul_eq_mul, mul_assoc]

/-- The common-radius bound also includes depth zero. -/
theorem norm_power_defect_le_common_radius (A B L : R) (n : ℕ) {ρ ε : ℝ}
    (hA : ‖A‖ ≤ ρ) (hB : ‖B‖ ≤ ρ) (hE : ‖B * L - L * A‖ ≤ ε) :
    ‖B ^ n * L - L * A ^ n‖ ≤ (n : ℝ) * ρ ^ (n - 1) * ε := by
  cases n with
  | zero => simp
  | succ n => simpa using norm_power_defect_succ_le A B L n hA hB hE

/-- With nonexpansive operators, the error grows at most linearly with depth. -/
theorem norm_power_defect_le_linear (A B L : R) (n : ℕ) {ε : ℝ}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (hE : ‖B * L - L * A‖ ≤ ε) :
    ‖B ^ n * L - L * A ^ n‖ ≤ (n : ℝ) * ε := by
  simpa using norm_power_defect_le_common_radius A B L n hA hB hE

/-- A strict contraction on the left gives a bound uniform in depth. -/
theorem norm_power_defect_le_geometric (A B L : R) (n : ℕ) {ρ ε : ℝ}
    (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ ρ) (hρ : ρ < 1)
    (hE : ‖B * L - L * A‖ ≤ ε) :
    ‖B ^ n * L - L * A ^ n‖ ≤ ε / (1 - ρ) := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg B).trans hB
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans hE
  have hseries : HasSum (fun j : ℕ => ρ ^ j) (1 - ρ)⁻¹ :=
    hasSum_geometric_of_abs_lt_one (by simpa [abs_of_nonneg hρ0] using hρ)
  have hgeom : ∑ j ∈ range n, ρ ^ j ≤ (1 - ρ)⁻¹ :=
    sum_le_hasSum (range n) (fun j _ => pow_nonneg hρ0 j) hseries
  calc
    ‖B ^ n * L - L * A ^ n‖ ≤
        ∑ j ∈ range n, ρ ^ j * ε * (1 : ℝ) ^ (n - 1 - j) :=
      norm_power_defect_le A B L n hA hB hE
    _ = (∑ j ∈ range n, ρ ^ j) * ε := by simp [Finset.sum_mul]
    _ ≤ (1 - ρ)⁻¹ * ε := mul_le_mul_of_nonneg_right hgeom hε0
    _ = ε / (1 - ρ) := by rw [div_eq_mul_inv, mul_comm]

/-- With a shared contraction bound, the error at successive depths tends to zero. -/
theorem power_defect_tendsto_zero (A B L : R) {ρ ε : ℝ}
    (hA : ‖A‖ ≤ ρ) (hB : ‖B‖ ≤ ρ) (hρ : ρ < 1)
    (hE : ‖B * L - L * A‖ ≤ ε) :
    Filter.Tendsto (fun n : ℕ => B ^ (n + 1) * L - L * A ^ (n + 1))
      Filter.atTop (nhds 0) := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg A).trans hA
  apply squeeze_zero_norm (fun n => norm_power_defect_succ_le A B L n hA hB hE)
  have h := (tendsto_self_mul_const_pow_of_lt_one hρ0 hρ).add
    (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ)
  simpa [Nat.cast_add, Nat.cast_one, add_mul] using h.mul_const ε

end NormEstimates

end Neoplatonic.LTR.ApproximateIntertwining
