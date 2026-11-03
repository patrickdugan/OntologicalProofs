import Mathlib

/-!
# A finite gluing obstruction

Three local one-bit completion spaces are joined by two identity transports
and one Boolean negation transport. Every transport is a bijection. Every
pair of edge constraints has a solution. The whole cycle has none.

Negation here acts on the two points of the completion space. It is induced
by the propositional substitution p ↦ ¬p; it is NOT the invalid proposal to
use complementation as a homomorphism of an arbitrary Boolean algebra.
All finite checks below use kernel-reduced `decide`, never `native_decide`.
-/

namespace Neoplatonic.LTR

/-- An elementary cyclic interface: equality, equality, one flip. -/
def triangleConstraint (k : Fin 3) (x : Fin 3 → Bool) : Prop :=
  if k = 0 then x 0 = x 1
  else if k = 1 then x 1 = x 2
  else x 2 = !(x 0)

instance (k : Fin 3) (x : Fin 3 → Bool) : Decidable (triangleConstraint k x) := by
  unfold triangleConstraint
  infer_instance

/-- Even every pair of edges can be simultaneously satisfied. -/
theorem triangle_pairwise_consistent :
    ∀ i j : Fin 3, ∃ x : Fin 3 → Bool,
      triangleConstraint i x ∧ triangleConstraint j x := by
  decide

/-- Yet the full diagram has no global compatible completion. -/
theorem triangle_no_global_section :
    ¬ ∃ x : Fin 3 → Bool, ∀ k : Fin 3, triangleConstraint k x := by
  decide

/-- The nontrivial edge transport is itself a bijection. -/
theorem bool_flip_bijective : Function.Bijective (fun b : Bool => !b) := by
  constructor
  · intro a b h
    cases a <;> cases b <;> simp_all
  · intro b
    exact ⟨!b, by cases b <;> rfl⟩

/-- A single unflipped local state extends across either individual edge. -/
theorem every_local_bit_extends_across_flip :
    ∀ b : Bool, ∃ c : Bool, c = !b := by
  intro b
  exact ⟨!b, rfl⟩

/-- The composite transport of a compatible cycle must fix its starting point. -/
theorem loop_requires_fixed_point
    {X : Type*} (f g h : X → X) {x y z : X}
    (hxy : y = f x) (hyz : z = g y) (hzx : x = h z) :
    h (g (f x)) = x := by
  rw [← hxy, ← hyz, ← hzx]

/-- The Boolean flip has no fixed point, explaining the obstruction. -/
theorem bool_flip_has_no_fixed_point :
    ¬ ∃ b : Bool, !b = b := by
  decide

end Neoplatonic.LTR
