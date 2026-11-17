import Neoplatonic.Arithmetic

/-!
# GK-01: remove the unit from the normalized gcd kernel

The positive-natural divisibility order in `Arithmetic.lean` has the
universal root 1. Removing it leaves nonunit common-ground structure,
already characterized there by non-coprimality.

The normalized gcd kernel splits algebraically into the universal
divisor's rank-one contribution and a nonunit remainder. This file
proves the decomposition and an exact Boolean support criterion.
It does not prove the remainder's positive semidefiniteness or claim
Riemann Hypothesis consequences. See idolum-ai/riemann-venue
`RiemannVenue/Kernels/GCD.lean` for the totient Gram factorization.
-/

namespace Neoplatonic.GroundKernel

/-- The unitless domain is the previously defined subtype of naturals >= 2. -/
abbrev World := Neoplatonic.NonUnit

/-- Exact common nonunit ground in the original divisibility reachability. -/
def CommonNonunitGround (m n : World) : Prop :=
  ∃ d : World, Reach divPrior₂ d m ∧ Reach divPrior₂ d n

/-- The normalized arithmetic gcd kernel (an external spectral counterpart
of the divisibility incidence relation). -/
noncomputable def normalizedGcd (m n : World) : ℝ :=
  (Nat.gcd m.val n.val : ℝ) /
    (Real.sqrt (m.val : ℝ) * Real.sqrt (n.val : ℝ))

/-- Universal divisor 1 contributes this rank-one kernel. -/
noncomputable def universalUnit (m n : World) : ℝ :=
  1 / (Real.sqrt (m.val : ℝ) * Real.sqrt (n.val : ℝ))

/-- The remaining arithmetic contribution after removing divisor 1. -/
noncomputable def nonunitRemainder (m n : World) : ℝ :=
  ((Nat.gcd m.val n.val : ℝ) - 1) /
    (Real.sqrt (m.val : ℝ) * Real.sqrt (n.val : ℝ))

noncomputable def unitVector (m : World) : ℝ :=
  (Real.sqrt (m.val : ℝ))⁻¹

/-- The universal term is an outer product of a single vector. -/
theorem universal_is_rank_one (m n : World) :
    universalUnit m n = unitVector m * unitVector n := by
  simp [universalUnit, unitVector, div_eq_mul_inv, mul_inv_rev]

/-- Exact decomposition of the normalized gcd kernel. -/
theorem normalized_kernel_splits (m n : World) :
    normalizedGcd m n = universalUnit m n + nonunitRemainder m n := by
  unfold normalizedGcd universalUnit nonunitRemainder
  ring

/-- The nonunit numerator is positive exactly when the states
have a common nonunit ancestor in the previously defined grounding order. -/
theorem remainder_support_iff_common_ground (m n : World) :
    0 < Nat.gcd m.val n.val - 1 ↔ CommonNonunitGround m n := by
  constructor
  · intro h
    have hg : 2 ≤ Nat.gcd m.val n.val := by omega
    refine ⟨⟨Nat.gcd m.val n.val, hg⟩, ?_, ?_⟩
    · exact reach₂_of_dvd (Nat.gcd_dvd_left _ _)
    · exact reach₂_of_dvd (Nat.gcd_dvd_right _ _)
  · rintro ⟨d, hd_m, hd_n⟩
    have hdiv : d.val ∣ Nat.gcd m.val n.val :=
      Nat.dvd_gcd (reach₂_dvd hd_m) (reach₂_dvd hd_n)
    have hpositive : 0 < Nat.gcd m.val n.val :=
      Nat.gcd_pos_of_pos_left _ (by omega)
    have hbound : d.val ≤ Nat.gcd m.val n.val :=
      Nat.le_of_dvd hpositive hdiv
    have hd : 2 ≤ d.val := d.property
    omega

/-- Existing arithmetic result expressed through the new kernel's
    nonunit support. -/
theorem remainder_support_iff_not_coprime (m n : World) :
    0 < Nat.gcd m.val n.val - 1 ↔ ¬ Nat.Coprime m.val n.val := by
  calc
    0 < Nat.gcd m.val n.val - 1 ↔ CommonNonunitGround m n :=
      remainder_support_iff_common_ground m n
    _ ↔ ¬ Nat.Coprime m.val n.val := by
      exact common_ground_iff_not_coprime m n

#print axioms universal_is_rank_one
#print axioms normalized_kernel_splits
#print axioms remainder_support_iff_common_ground
#print axioms remainder_support_iff_not_coprime

end Neoplatonic.GroundKernel
