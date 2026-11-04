import Mathlib.Tactic

/-!
# Centered symmetry does not imply the Riemann hypothesis

An abstract, finite, rational-valued spectrum has the same reflection
symmetry of real coordinates that the functional equation gives the
nontrivial zeta zeros. It may nonetheless contain off-axis points.

This file proves elementary symmetry facts and a countermodel to the
implication "reflection closure -> all points on the critical line".
It does not claim to construct a nontrivial zero of the zeta function.
-/

namespace GrammyAndPrimes

/-- Reflection about the rational coordinate 1/2. -/
def mirror (x : ℚ) : ℚ := 1 - x

theorem mirror_involution (x : ℚ) : mirror (mirror x) = x := by
  dsimp [mirror]
  ring

/-- A point is individually fixed by the reflection exactly when it lies
    at the critical real coordinate 1/2. -/
theorem mirror_fixed_iff_center (x : ℚ) :
    mirror x = x ↔ x = (1 / 2 : ℚ) := by
  dsimp [mirror]
  constructor <;> intro h <;> linarith

/-- Each reflection orbit has its arithmetic mean at the critical line. -/
theorem mirror_pair_mean (x : ℚ) :
    (x + mirror x) / 2 = (1 / 2 : ℚ) := by
  dsimp [mirror]
  ring

/-- A concrete two-point spectrum centered around 1/2. -/
def toyCoordinate : Bool → ℚ
  | false => 1 / 3
  | true => 2 / 3

/-- The two points are exchanged by reflection. -/
theorem toy_reflection (b : Bool) :
    toyCoordinate (!b) = mirror (toyCoordinate b) := by
  cases b <;> norm_num [toyCoordinate, mirror]

/-- The toy spectrum has the required setwise reflection symmetry. -/
theorem toy_closed_under_reflection :
    ∀ b : Bool, ∃ c : Bool,
      toyCoordinate c = mirror (toyCoordinate b) := by
  intro b
  exact ⟨!b, toy_reflection b⟩

/-- It is centered but an individual coordinate lies off the line. -/
theorem toy_has_off_axis_point :
    ∃ b : Bool, toyCoordinate b ≠ (1 / 2 : ℚ) := by
  refine ⟨false, ?_⟩
  norm_num [toyCoordinate]

/-- Reflection closure of a spectrum is insufficient for alignment. -/
theorem reflection_closure_not_sufficient :
    ¬ (∀ coord : Bool → ℚ,
      (∀ b : Bool, ∃ c : Bool, coord c = mirror (coord b)) →
      (∀ b : Bool, coord b = (1 / 2 : ℚ))) := by
  intro h
  have hcenter : ∀ b : Bool, toyCoordinate b = (1 / 2 : ℚ) :=
    h toyCoordinate toy_closed_under_reflection
  obtain ⟨b, hb⟩ := toy_has_off_axis_point
  exact hb (hcenter b)

/-- Stronger pointwise fixedness, unlike setwise reflection closure,
    is enough to force every coordinate to the line. -/
theorem pointwise_fixed_implies_alignment {α : Type*}
    (coord : α → ℚ)
    (hfixed : ∀ a : α, mirror (coord a) = coord a) :
    ∀ a : α, coord a = (1 / 2 : ℚ) := by
  intro a
  exact (mirror_fixed_iff_center (coord a)).mp (hfixed a)

/-- This model has a nonzero mean square deviation from the critical line,
    even though the mean coordinate is 1/2. -/
theorem toy_positive_deviation :
    ((toyCoordinate false - (1 / 2 : ℚ)) ^ 2 +
      (toyCoordinate true - (1 / 2 : ℚ)) ^ 2) = (1 / 18 : ℚ) := by
  norm_num [toyCoordinate]

end GrammyAndPrimes
