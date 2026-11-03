import Neoplatonic.LTR.SpectralBridge

/-!
# Exact marked-edge Lipschitz and metric reconstruction

For an abstract metric space X whose distinct ordered pairs have
a countable marked enumeration, take the off-diagonal Dirac scale
s_j = 1 / dist(left_j,right_j).

The unit edge-gradient condition is exactly the global real
1-Lipschitz condition. The distance-to-a-point observable then
witnesses equality in the Connes-style dual distance formula.

For uncountable compact Stone completions, the countable marking
instead enumerates pairs of a dense subset. Extending the result to
all X then needs the explicit continuity/density argument.
-/

namespace Neoplatonic.LTR

/-- Exact scaled difference quotient of a real observable along
a nondegenerate metric edge. -/
theorem markedEdgeInvDist_norm
    {X : Type*} [MetricSpace X]
    (x y : X) (hxy : x ≠ y) (a : X → ℝ) :
    |(dist x y)⁻¹ * (a y - a x)| =
      |a x - a y| / dist x y := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hd.le),
    abs_sub_comm (a y) (a x), div_eq_mul_inv, mul_comm]

/-- A reciprocal-distance edge gradient bound is equivalent to the
corresponding Lipschitz bound along the original metric edge. -/
theorem markedEdgeBound_iff
    {X : Type*} [MetricSpace X]
    (x y : X) (hxy : x ≠ y) (a : X → ℝ) (L : ℝ) :
    |(dist x y)⁻¹ * (a y - a x)| ≤ L ↔
      |a x - a y| ≤ L * dist x y := by
  rw [markedEdgeInvDist_norm x y hxy a]
  exact div_le_iff₀ (dist_pos.mpr hxy)

/-- If the marking includes all ordered distinct pairs, its unit
edge-gradient tests are equivalent to global Lipschitz continuity. -/
theorem markedEdgeUnitBound_iff_lipschitz
    {X : Type*} [MetricSpace X]
    (left right : ℕ → X)
    (hdistinct : ∀ j, left j ≠ right j)
    (hcover : ∀ x y : X, x ≠ y →
      ∃ j : ℕ, left j = x ∧ right j = y)
    (a : X → ℝ) :
    (∀ j, |(dist (left j) (right j))⁻¹ *
      (a (right j) - a (left j))| ≤ 1) ↔
    (∀ x y, |a x - a y| ≤ dist x y) := by
  constructor
  · intro hedge x y
    by_cases hxy : x = y
    · subst y
      simp
    · obtain ⟨j, hjx, hjy⟩ := hcover x y hxy
      have h := (markedEdgeBound_iff
        (left j) (right j) (hdistinct j) a 1).mp (hedge j)
      simpa [hjx, hjy] using h
  · intro hlip j
    apply (markedEdgeBound_iff
      (left j) (right j) (hdistinct j) a 1).mpr
    simpa only [one_mul] using hlip (left j) (right j)

/-- Exact distance recovery from marked reciprocal-distance edge tests:
all unit-gradient observables satisfy the metric bound, and the
distance-to-target observable attains it. -/
theorem markedEdgeConnesDistance_witness
    {X : Type*} [MetricSpace X]
    (left right : ℕ → X)
    (hdistinct : ∀ j, left j ≠ right j)
    (hcover : ∀ x y : X, x ≠ y →
      ∃ j : ℕ, left j = x ∧ right j = y)
    (x y : X) :
    (∀ a : X → ℝ,
      (∀ j, |(dist (left j) (right j))⁻¹ *
        (a (right j) - a (left j))| ≤ 1) →
      |a x - a y| ≤ dist x y) ∧
    ∃ a : X → ℝ,
      (∀ j, |(dist (left j) (right j))⁻¹ *
        (a (right j) - a (left j))| ≤ 1) ∧
      |a x - a y| = dist x y := by
  obtain ⟨hupper, ⟨a, ha, heq⟩⟩ := metric_recovery_witness x y
  constructor
  · intro f hf
    exact hupper f
      ((markedEdgeUnitBound_iff_lipschitz
        left right hdistinct hcover f).mp hf)
  · exact ⟨a,
      (markedEdgeUnitBound_iff_lipschitz
        left right hdistinct hcover a).mpr ha,
      heq⟩

end Neoplatonic.LTR
