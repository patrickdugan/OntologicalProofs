import Neoplatonic.LTR.NullarySemantics

/-!
# Singleton-domain model classification

Every nonempty model of the one-axiom nullary language is a singleton.
Its complete first-order theory is determined by the Boolean values of
its nullary relations. This is the semantic key to reconstructing
all complete types and eventually a Cantor-space homeomorphism.

No new axiom, sorry, or assumed quantifier elimination is used.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.Structure

/-- The sole nonlogical axiom forces every nonempty model to have one element. -/
theorem subsingleton_of_model_T (M : Type*) [L.Structure M]
    [Nonempty M] [M ⊨ T] : Subsingleton M := by
  have haxiom : M ⊨ (FirstOrder.Language.Sentence.cardGe L 2).not := by
    exact FirstOrder.Language.Theory.realize_sentence_of_mem T (by simp [T])
  have hsmall : ¬ (2 : Cardinal) ≤ Cardinal.mk M := by
    simpa [FirstOrder.Language.Sentence.realize_not,
      FirstOrder.Language.Sentence.realize_cardGe] using haxiom
  constructor
  intro a b
  by_contra hab
  apply hsmall
  exact Cardinal.two_le_iff.mpr ⟨a, b, hab⟩

/-- A Boolean stream extracted from actual nullary relation truth values. -/
noncomputable def modelBits (M : Type*) [L.Structure M] : ℕ → Bool :=
  fun n => by
    classical
    exact decide (@RelMap L M _ 0 (predSym n) (fun i : Fin 0 => Fin.elim0 i))

/-- The original model's nullary relations have exactly these truth values. -/
theorem modelBits_iff (M : Type*) [L.Structure M] (n : ℕ) :
    modelBits M n = true ↔
      @RelMap L M _ 0 (predSym n) (fun i : Fin 0 => Fin.elim0 i) := by
  classical
  simp [modelBits]

/-- The original model's nullary sentences have these truth values. -/
theorem modelBits_atom (M : Type*) [L.Structure M] (n : ℕ) :
    (M ⊨ atom n) ↔ modelBits M n = true := by
  change (@RelMap L M _ 0 (predSym n)
      (fun i : Fin 0 => Fin.elim0 i)) ↔ modelBits M n = true
  exact (modelBits_iff M n).symm

/-- A nonempty subsingleton structure is isomorphic to its Boolean singleton model. -/
noncomputable def modelIsoUnit (M : Type*) [L.Structure M]
    [Nonempty M] [Subsingleton M] :
    @FirstOrder.Language.Equiv L M Unit inferInstance (unitStructure (modelBits M)) := by
  classical
  letI : Inhabited M := Classical.inhabited_of_nonempty'
  letI : Unique M := Unique.mk' M
  letI : L.Structure Unit := unitStructure (modelBits M)
  refine { Equiv.ofUnique M Unit with
    map_fun' := ?_
    map_rel' := ?_ }
  · intro n f xs
    exact nomatch f
  · intro n r xs
    cases n with
    | zero =>
        change (modelBits M r = true) ↔
          @RelMap L M _ 0 r xs
        rw [modelBits_iff]
        rfl
    | succ n => exact nomatch r

/-- The entire first-order sentence theory of a singleton model is
recovered from its sequence of nullary truth values. -/
theorem all_sentences_of_modelBits (M : Type*) [L.Structure M]
    [Nonempty M] [Subsingleton M] (φ : L.Sentence) :
    (M ⊨ φ) ↔
      @FirstOrder.Language.Sentence.Realize L Unit (unitStructure (modelBits M)) φ := by
  classical
  letI : L.Structure Unit := unitStructure (modelBits M)
  exact (modelIsoUnit M).realize_sentence φ

end Neoplatonic.LTR.Nullary
