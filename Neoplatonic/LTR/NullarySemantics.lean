import Neoplatonic.LTR.NullaryTypes
import Neoplatonic.LTR.NullaryHalting

/-!
# Semantic realization of all first-order formulas under predicate renaming

The nullary language endomorphism is interpreted by pulling back the
one-element model's structure. Mathlib's general LHom.realize_onSentence
then gives the truth equivalence for *all* sentences, including quantified
sentences. We state every instance explicitly where source and target
languages happen to be definitionally equal.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language

/-- The reduct of a Boolean model along an index renaming is exactly
the Boolean model of the reindexed stream. -/
theorem rename_reduct (σ : ℕ → ℕ) (bits : ℕ → Bool) :
    (letI : L.Structure Unit := unitStructure bits
     (rename σ).reduct Unit) = unitStructure (bits ∘ σ) := by
  letI : L.Structure Unit := unitStructure bits
  apply FirstOrder.Language.Structure.ext
  · intro n f xs
    exact isEmptyElim f
  · intro n r xs
    cases n with
    | zero => rfl
    | succ n => exact isEmptyElim r

/-- Full first-order sentence semantics, independent of the formula's
quantifier structure. -/
theorem rename_realizes_sentence (σ : ℕ → ℕ)
    (bits : ℕ → Bool) (φ : L.Sentence) :
    @FirstOrder.Language.Sentence.Realize L Unit (unitStructure bits)
      ((rename σ).onSentence φ) ↔
    @FirstOrder.Language.Sentence.Realize L Unit (unitStructure (bits ∘ σ)) φ := by
  letI : L.Structure Unit := unitStructure bits
  have h :
      @FirstOrder.Language.Sentence.Realize L Unit (unitStructure bits)
        ((rename σ).onSentence φ) ↔
      @FirstOrder.Language.Sentence.Realize L Unit ((rename σ).reduct Unit) φ :=
    @FirstOrder.Language.LHom.realize_onSentence L L Unit
      ((rename σ).reduct Unit) (unitStructure bits)
      (rename σ)
      (FirstOrder.Language.LHom.isExpansionOn_reduct (rename σ) Unit) φ
  rw [rename_reduct σ bits] at h
  exact h

/-- A halting-index syntactic substitution realizes exactly the full
first-order theory of the transformed Cantor stream. -/
theorem haltingRename_realizes_sentence
    (e : Nat.Partrec.Code) (bits : ℕ → Bool) (φ : L.Sentence) :
    @FirstOrder.Language.Sentence.Realize L Unit (unitStructure bits)
      ((haltingRename e).onSentence φ) ↔
    @FirstOrder.Language.Sentence.Realize L Unit
      (unitStructure (acceleratedStream (stagedHalting e) bits)) φ := by
  have hb : (bits ∘ haltingIndex e) =
      acceleratedStream (stagedHalting e) bits := by
    funext n
    exact haltingIndex_stream e bits n
  change @FirstOrder.Language.Sentence.Realize L Unit (unitStructure bits)
      ((rename (haltingIndex e)).onSentence φ) ↔
    @FirstOrder.Language.Sentence.Realize L Unit
      (unitStructure (acceleratedStream (stagedHalting e) bits)) φ
  rw [← hb]
  exact rename_realizes_sentence (haltingIndex e) bits φ

end Neoplatonic.LTR.Nullary
