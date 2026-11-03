import Neoplatonic.LTR.SpectralBridge
import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Resolvent tails and compactness of an infinite Dirac direct sum

For the mass-shifted block D_j with mass m_j >= 2^j, the squared
resolvent (I+D_j²)^(-1) is scalar with coefficient

    r_j = 1 / (1 + m_j² + s_j²) <= 1 / (1 + 4^j).

This file checks the exact tail estimate and its convergence to zero.

It also packages the compact-operator closure step: if bounded
operators R_N have finite-dimensional range (hence are compact)
and their operator-norm distance from the candidate squared
resolvent R is bounded by 1/(1+4^N), then R is compact.

Construction of R and R_N as maps on ℓ²(ℕ,ℂ²), the unbounded Dirac
domain, and the estimate in that specific setting are separate
proof obligations. The compactness implication itself is kernel checked.
-/

namespace Neoplatonic.LTR

open Filter

/-- Canonical scalar tail bound for the squared resolvent. -/
noncomputable def squaredResolventTail (n : ℕ) : ℝ :=
  (1 + (4 : ℝ)^n)⁻¹

theorem squaredResolventTail_nonneg (n : ℕ) :
    0 ≤ squaredResolventTail n := by
  unfold squaredResolventTail
  positivity

/-- This positive tail bound tends to zero exponentially. -/
theorem squaredResolventTail_tendsto :
    Tendsto squaredResolventTail atTop (𝓝 (0 : ℝ)) := by
  have hp : Tendsto (fun n : ℕ => (4 : ℝ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have ha : Tendsto (fun n : ℕ => (4 : ℝ)^n + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hp
  have hz : Tendsto (fun n : ℕ => ((4 : ℝ)^n + 1)⁻¹)
      atTop (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero.comp ha
  simpa only [squaredResolventTail, add_comm] using hz

/-- Exact bound on the squared resolvent coefficient at any block,
provided its mass is at least 2^j. Arbitrary off-diagonal couplings
make the bound only smaller. -/
theorem block_squaredResolvent_le_tail
    (mass scale : ℕ → ℝ)
    (hmass : ∀ j, (2 : ℝ)^j ≤ mass j)
    (j : ℕ) :
    1 / (1 + (mass j)^2 + (scale j)^2) ≤ squaredResolventTail j := by
  have h := mass_resolvent_bound (mass j) (scale j)
    ((2 : ℝ)^j) (by positivity) (hmass j)
  have hp : ((2 : ℝ)^j)^2 = (4 : ℝ)^j := by
    rw [pow_two, ← mul_pow]
    norm_num
  simpa [squaredResolventTail, hp, one_div] using h

/-- The analytic closure step of compact resolvent, stated for
actual continuous linear maps. No unproved compactness principle
is introduced: mathlib supplies the norm-closed compact-operator
theorem. -/
theorem compact_of_squaredResolvent_tail
    {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (R : E →L[ℝ] E) (Rfinite : ℕ → E →L[ℝ] E)
    (hfinite : ∀ N, IsCompactOperator (Rfinite N))
    (hbound : ∀ N, ‖R - Rfinite N‖ ≤ squaredResolventTail N) :
    IsCompactOperator R := by
  have hn : Tendsto (fun N => ‖Rfinite N - R‖) atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero (fun N => norm_nonneg _) (fun N => ?_)
      squaredResolventTail_tendsto
    simpa only [norm_sub_rev] using hbound N
  have hlim : Tendsto Rfinite atTop (𝓝 R) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hn
  exact isCompactOperator_of_tendsto hlim
    (Filter.Eventually.of_forall hfinite)

end Neoplatonic.LTR
