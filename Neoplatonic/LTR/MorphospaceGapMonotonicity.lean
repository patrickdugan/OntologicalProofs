import Neoplatonic.LTR.MorphospaceInformationCover
import Mathlib

/-!
# MOR-09: nested evidence implies monotone certification gap

This is a witness-explicit finite-minimum theorem over rational bounds.
It formalizes the deterministic invariant behind QO-11's active probe
selector, not its Bayesian planning predictive or the separate QO-07
anytime Ville confidence theorem.
-/

namespace Neoplatonic.LTR.Morphospace

universe u

/-- Lower and upper interval endpoints refined inward have a
weakly smaller Chebyshev radius. -/
theorem robust_interval_radius_refinement
    (oldLo oldHi newLo newHi : ℚ)
    (hlo : oldLo ≤ newLo) (hhi : newHi ≤ oldHi) :
    (newHi - newLo) / 2 ≤ (oldHi - oldLo) / 2 := by
  linarith

/-- Inward refinements weakly increase the positive part of a
certified lower separation. -/
theorem optimistic_separation_refinement
    (oldLo oldHi newLo newHi : ℚ)
    (hlo : oldLo ≤ newLo) (hhi : newHi ≤ oldHi) :
    max (0 : ℚ) (oldLo - oldHi) ≤
      max (0 : ℚ) (newLo - newHi) := by
  apply max_le
  · exact le_max_left _ _
  · have h : oldLo - oldHi ≤ newLo - newHi := by linarith
    exact le_trans h (le_max_right _ _)

/-- Pointwise shrinking upper bounds shrink the MINIMUM upper bound.
The two named indices are certified minimizers in the finite
family of candidate partitions. -/
theorem robust_minimum_refinement
    {I : Type u}
    (oldUpper newUpper : I → ℚ)
    (oldWinner newWinner : I)
    (hNewMin : ∀ i, newUpper newWinner ≤ newUpper i)
    (hUpper : ∀ i, newUpper i ≤ oldUpper i) :
    newUpper newWinner ≤ oldUpper oldWinner :=
  (hNewMin oldWinner).trans (hUpper oldWinner)

/-- Pointwise larger optimistic lower bounds increase the MINIMUM
lower bound over a fixed family of partitions. -/
theorem optimistic_minimum_refinement
    {I : Type u}
    (oldLower newLower : I → ℚ)
    (oldWinner newWinner : I)
    (hOldMin : ∀ i, oldLower oldWinner ≤ oldLower i)
    (hLower : ∀ i, oldLower i ≤ newLower i) :
    oldLower oldWinner ≤ newLower newWinner :=
  (hOldMin newWinner).trans (hLower newWinner)

/-- The difference between optimized robust and optimistic bounds is
nonnegative and weakly decreases for every nonempty nested evidence
region, provided the partition family and outcome contract are fixed. -/
theorem certification_gap_monotone
    {I : Type u}
    (oldUpper newUpper oldLower newLower : I → ℚ)
    (oldUpperWinner newUpperWinner oldLowerWinner newLowerWinner : I)
    (hNewUpperMin : ∀ i, newUpper newUpperWinner ≤ newUpper i)
    (hOldLowerMin : ∀ i, oldLower oldLowerWinner ≤ oldLower i)
    (hNewLowerMin : ∀ i, newLower newLowerWinner ≤ newLower i)
    (hUpper : ∀ i, newUpper i ≤ oldUpper i)
    (hLower : ∀ i, oldLower i ≤ newLower i)
    (hNewValid : ∀ i, newLower i ≤ newUpper i) :
    (0 : ℚ) ≤ newUpper newUpperWinner - newLower newLowerWinner ∧
      newUpper newUpperWinner - newLower newLowerWinner ≤
        oldUpper oldUpperWinner - oldLower oldLowerWinner := by
  have hR := robust_minimum_refinement
    oldUpper newUpper oldUpperWinner newUpperWinner hNewUpperMin hUpper
  have hL := optimistic_minimum_refinement
    oldLower newLower oldLowerWinner newLowerWinner hOldLowerMin hLower
  have hNonneg : newLower newLowerWinner ≤ newUpper newUpperWinner :=
    (hNewLowerMin newUpperWinner).trans (hNewValid newUpperWinner)
  constructor <;> linarith

/-- Once a robust upper error is below the target tolerance, subsequent
valid nested refinements preserve the feasible certificate. -/
theorem feasible_certificate_persistent
    (oldUpper newUpper tolerance : ℚ)
    (hRefine : newUpper ≤ oldUpper)
    (hCertified : oldUpper ≤ tolerance) :
    newUpper ≤ tolerance :=
  hRefine.trans hCertified

/-- Once an optimistic lower bound is strictly above tolerance, later
valid refinements preserve the infeasible certificate. -/
theorem infeasible_certificate_persistent
    (oldLower newLower tolerance : ℚ)
    (hRefine : oldLower ≤ newLower)
    (hCertified : tolerance < oldLower) :
    tolerance < newLower :=
  lt_of_lt_of_le hCertified hRefine

/-- Deterministic nonnegativity of an expected one-step gain when
every hypothetical next gap is no greater than the present gap.
The Bernoulli predictive weight is a *planning* parameter. -/
theorem expected_gap_reduction_nonnegative
    (now nextHold nextHit p : ℚ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hHold : nextHold ≤ now)
    (hHit : nextHit ≤ now) :
    0 ≤ now - ((1 - p) * nextHold + p * nextHit) := by
  nlinarith

end Neoplatonic.LTR.Morphospace
