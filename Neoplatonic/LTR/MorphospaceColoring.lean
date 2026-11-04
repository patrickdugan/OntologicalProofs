import Neoplatonic.LTR.MorphospaceGoalFuture
import Mathlib

/-!
# MOR-05: intervention conflict graph and proper coloring

This formalizes the combinatorial core of the QO-03 reduction from
graph 3-coloring to bounded-error macrostate aggregation, at the local
rate-vector level. The NP-completeness statement itself is not
formalized here. Theorems have no extra axioms and assert nothing
about nonphysical causation or biological minds.
-/

namespace Neoplatonic.LTR.Morphospace

universe u
variable {V : Type u} [DecidableEq V]

/-- An edge action has hit probability 0 at its first endpoint, 1 at
its other endpoint, and 1/2 at every other transient state. -/
def edgeHitRate (u v s : V) : ℚ :=
  if s = u then 0 else if s = v then 1 else 1 / 2

/-- A single edge action separates a pair by more than 1/2 precisely
when the pair consists of the two distinct endpoints. -/
theorem edgeRate_large_iff_endpoints (u v s t : V) (huv : u ≠ v) :
    (1 / 2 : ℚ) < |edgeHitRate u v s - edgeHitRate u v t| ↔
      (s = u ∧ t = v) ∨ (s = v ∧ t = u) := by
  by_cases hsu : s = u
  <;> by_cases hsv : s = v
  <;> by_cases htu : t = u
  <;> by_cases htv : t = v
  <;> simp_all [edgeHitRate]
  <;> norm_num

/-- A proper 3-coloring of every specified oriented edge is equivalent
to a rate-consistent partition at tolerance 1/4 in the hit/hold
model: same-color states differ in rate by at most 1/2 for every
edge-indexed action. This is the local graph-theoretic statement.
-/
theorem proper_coloring_iff_rate_safe
    (E : Set (V × V))
    (hSimple : ∀ e ∈ E, e.1 ≠ e.2)
    (c : V → Fin 3) :
    (∀ e ∈ E, c e.1 ≠ c e.2) ↔
    (∀ e ∈ E, ∀ s t : V, c s = c t →
      |edgeHitRate e.1 e.2 s - edgeHitRate e.1 e.2 t| ≤ (1 / 2 : ℚ)) := by
  constructor
  · intro hColor e he s t hSame
    by_contra hUnsafe
    have hLarge : (1 / 2 : ℚ) <
        |edgeHitRate e.1 e.2 s - edgeHitRate e.1 e.2 t| :=
      lt_of_not_ge hUnsafe
    rcases (edgeRate_large_iff_endpoints e.1 e.2 s t (hSimple e he)).mp
        hLarge with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · have hEq : c e.1 = c e.2 := by simpa [hs, ht] using hSame
      exact (hColor e he) hEq
    · have hEq : c e.1 = c e.2 := by simpa [hs, ht] using hSame.symm
      exact (hColor e he) hEq
  · intro hSafe e he hSame
    have hBound := hSafe e he e.1 e.2 hSame
    have hLarge : (1 / 2 : ℚ) <
        |edgeHitRate e.1 e.2 e.1 - edgeHitRate e.1 e.2 e.2| :=
      (edgeRate_large_iff_endpoints e.1 e.2 e.1 e.2
        (hSimple e he)).mpr (Or.inl ⟨rfl, rfl⟩)
    exact (not_lt_of_ge hBound) hLarge

end Neoplatonic.LTR.Morphospace
