/-!
E8: Locally compatible readings need not give a global section.
Kripke accessibility here is *epistemic admissibility of interpretations*.
-/
import Init
namespace DivineElegance
universe u

abbrev Predicate (W : Type u) := W → Prop

def Box {W : Type u} (R : W → W → Prop) (P : Predicate W) (w : W) : Prop :=
  ∀ v, R w v → P v

def Diamond {W : Type u} (R : W → W → Prop) (P : Predicate W) (w : W) : Prop :=
  ∃ v, R w v ∧ P v

theorem necessity_survives_evidence_refinement {W : Type u}
    (old new : W → W → Prop) (p : Predicate W) (w : W)
    (narrows : ∀ x y, new x y → old x y)
    (h : Box old p w) : Box new p w := by
  intro v hv
  exact h v (narrows w v hv)

theorem surviving_possibility_was_previously_possible {W : Type u}
    (old new : W → W → Prop) (p : Predicate W) (w : W)
    (narrows : ∀ x y, new x y → old x y)
    (h : Diamond new p w) : Diamond old p w := by
  cases h with
  | intro v hv =>
    exact ⟨v, narrows w v hv.1, hv.2⟩

/-- A three-edge XOR parity obstruction: x=y, y=z, and x≠z. -/
theorem parity_pairwise_satisfiable :
    (∃ x y z : Bool, x = y ∧ y = z) ∧
    (∃ x y z : Bool, y = z ∧ x ≠ z) ∧
    (∃ x y z : Bool, x = y ∧ x ≠ z) := by
  constructor
  · exact ⟨false, false, false, rfl, rfl⟩
  constructor
  · exact ⟨true, false, false, rfl, by decide⟩
  · exact ⟨false, false, true, rfl, by decide⟩

theorem parity_no_global_solution :
    ¬ (∃ x y z : Bool, x = y ∧ y = z ∧ x ≠ z) := by
  intro h
  cases h with
  | intro x hx =>
    cases hx with
    | intro y hy =>
      cases hy with
      | intro z hz =>
        exact hz.2.2 (hz.1.trans hz.2.1)

/-- A chosen outward/inward layer relation, not a Ṣadrian historical theorem. -/
structure Layers (W : Type u) where
  zahir : W → Prop
  batin : W → Prop
  preservation : ∀ w, batin w → zahir w

theorem inner_layer_preserves_outer {W : Type u} (l : Layers W)
    (w : W) : ¬ (l.batin w ∧ ¬ l.zahir w) := by
  intro h
  exact h.2 (l.preservation w h.1)

end DivineElegance
