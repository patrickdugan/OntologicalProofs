import Neoplatonic.LTR.Nullary

/-!
# Independent atomic sentences in the one-axiom theory

Both truth values of every nullary predicate are realized by explicit
one-element models. This gives actual non-entailment theorems in mathlib
semantics rather than treating independence as a structural assumption.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language

/-- The finite-axiom theory does not force any individual nullary atom. -/
theorem not_entails_atom (n : ℕ) : ¬ (T ⊨ᵇ atom n) := by
  intro h
  let bits : ℕ → Bool := fun _ => false
  letI : L.Structure Unit := unitStructure bits
  letI : Unit ⊨ T := unit_models_T bits
  have ht : Unit ⊨ atom n := h.realize_sentence Unit
  have hb : bits n = true := (unit_realizes_atom bits n).mp ht
  simp [bits] at hb

/-- The finite-axiom theory likewise does not force the negation. -/
theorem not_entails_not_atom (n : ℕ) : ¬ (T ⊨ᵇ (atom n).not) := by
  intro h
  let bits : ℕ → Bool := fun _ => true
  letI : L.Structure Unit := unitStructure bits
  letI : Unit ⊨ T := unit_models_T bits
  have ht : Unit ⊨ (atom n).not := h.realize_sentence Unit
  have hyes : Unit ⊨ atom n := (unit_realizes_atom bits n).mpr (by simp [bits])
  exact (FirstOrder.Language.Sentence.realize_not (M := Unit)).mp ht hyes

/-- Every nullary predicate is independent of the single nonlogical axiom. -/
theorem independent_atom (n : ℕ) :
    ¬ (T ⊨ᵇ atom n) ∧ ¬ (T ⊨ᵇ (atom n).not) :=
  ⟨not_entails_atom n, not_entails_not_atom n⟩

end Neoplatonic.LTR.Nullary
