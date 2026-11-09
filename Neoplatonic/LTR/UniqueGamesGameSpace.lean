import Neoplatonic.LTR.UniqueGamesFinite

/-!
# UGCS-01: finite holonomy obstructions and lifted-edge consistency

This formalizes elementary algebraic lemmas used by the four game-space
research conjectures. It does not claim a proof of any of the conjectures
or reproduce the upstream Unique Games reduction.
-/

namespace Neoplatonic.LTR.UniqueGames.GameSpace

variable {K : Type*} [AddCommGroup K]

/-- An exactly satisfied triangle has zero additive holonomy. -/
theorem triangle_holonomy_zero
    (a0 a1 a2 c01 c12 c20 : K)
    (h01 : a1 - a0 = c01)
    (h12 : a2 - a1 = c12)
    (h20 : a0 - a2 = c20) :
    c01 + c12 + c20 = 0 := by
  rw [← h01, ← h12, ← h20]
  abel

/-- Nonzero cycle holonomy rules out a globally satisfying triangle. -/
theorem frustrated_triangle_no_section
    (c01 c12 c20 : K)
    (hhol : c01 + c12 + c20 ≠ 0) :
    ¬ ∃ a0 a1 a2 : K,
      a1 - a0 = c01 ∧ a2 - a1 = c12 ∧ a0 - a2 = c20 := by
  rintro ⟨a0, a1, a2, h01, h12, h20⟩
  exact hhol (triangle_holonomy_zero a0 a1 a2 c01 c12 c20 h01 h12 h20)

/-- The cycle sum is unchanged by a vertex gauge transformation. -/
theorem triangle_holonomy_gauge
    (c01 c12 c20 p0 p1 p2 : K) :
    (c01 + (p1 - p0)) + (c12 + (p2 - p1)) +
      (c20 + (p0 - p2)) = c01 + c12 + c20 := by
  abel

/-- Local calculation behind the regular holonomy-cover labeling.
    The sheet coordinate changes by the normalized edge residual. -/
theorem lifted_edge_satisfied
    (pSource pTarget sheet residual shift : K)
    (hshift : shift = pTarget - pSource + residual) :
    (pTarget + (sheet + residual)) - (pSource + sheet) = shift := by
  rw [hshift]
  abel

end Neoplatonic.LTR.UniqueGames.GameSpace

#print axioms Neoplatonic.LTR.UniqueGames.GameSpace.triangle_holonomy_zero
#print axioms Neoplatonic.LTR.UniqueGames.GameSpace.frustrated_triangle_no_section
#print axioms Neoplatonic.LTR.UniqueGames.GameSpace.triangle_holonomy_gauge
#print axioms Neoplatonic.LTR.UniqueGames.GameSpace.lifted_edge_satisfied
