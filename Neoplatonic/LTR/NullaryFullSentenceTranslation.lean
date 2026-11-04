import Neoplatonic.LTR.NumberedSemanticMapComposition
import Neoplatonic.LTR.NullaryEndomorphisms

/-!
# Complete expanded-sentence semantics of the nullary syntax maps

Mathlib's language equivalence for adding no constant symbols
identifies the entire original first-order sentence type with
the expanded-language sentence type underlying CompleteType Empty.
This fills the semantic coverage gap between the existing theorem
for lifted original-language sentences and the numbered geometric
results, which require all sentences of the expanded language.

The transformed sentence is constructed by transporting to the
original language, applying the genuine syntactic language
endomorphism, and transporting back. The result applies to
arbitrary quantified expanded-language sentences.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language

/-- Empty-constant expansion induces an equivalence of all
original and expanded first-order sentences. -/
def emptyConstantSentenceEquiv : L.Sentence ≃ L[[Empty]].Sentence :=
  (LEquiv.addEmptyConstants L Empty).onSentence

/-- The sentence equivalence uses exactly the previously defined
injection of original sentences into the empty expansion. -/
theorem emptyConstantSentenceEquiv_apply (φ : L.Sentence) :
    emptyConstantSentenceEquiv φ = liftedSentence φ := by
  rfl

/-- Explicit inverse translation of arbitrary expanded sentences. -/
def unliftExpandedSentence (ψ : L[[Empty]].Sentence) : L.Sentence :=
  emptyConstantSentenceEquiv.symm ψ

theorem lift_unliftExpandedSentence (ψ : L[[Empty]].Sentence) :
    liftedSentence (unliftExpandedSentence ψ) = ψ := by
  change emptyConstantSentenceEquiv
    (emptyConstantSentenceEquiv.symm ψ) = ψ
  exact emptyConstantSentenceEquiv.apply_symm_apply ψ

theorem unliftExpandedSentence_lift (φ : L.Sentence) :
    unliftExpandedSentence (liftedSentence φ) = φ := by
  change emptyConstantSentenceEquiv.symm
    (emptyConstantSentenceEquiv φ) = φ
  exact emptyConstantSentenceEquiv.symm_apply_apply φ

/-- The genuine full-language substitution on all sentences of the
empty-constant expansion, including quantified sentences. -/
def expandedHaltingRename (e : Nat.Partrec.Code)
    (ψ : L[[Empty]].Sentence) : L[[Empty]].Sentence :=
  liftedSentence ((haltingRename e).onSentence
    (unliftExpandedSentence ψ))

/-- On a lifted original sentence this agrees exactly with the
original syntactic endomorphism. -/
theorem expandedHaltingRename_lifted (e : Nat.Partrec.Code)
    (φ : L.Sentence) :
    expandedHaltingRename e (liftedSentence φ) =
      liftedSentence ((haltingRename e).onSentence φ) := by
  simp [expandedHaltingRename, unliftExpandedSentence_lift]

/-- Full expanded-language sentence truth pulls back under the
actual nullary complete-type map through the syntax translation. -/
theorem syntaxMap_expanded_semantics (e : Nat.Partrec.Code)
    (p : T.CompleteType Empty) (ψ : L[[Empty]].Sentence) :
    ψ ∈ syntaxMap e p ↔ expandedHaltingRename e ψ ∈ p := by
  simpa only [expandedHaltingRename, lift_unliftExpandedSentence]
    using (syntaxMap_semantics e p (unliftExpandedSentence ψ))

end Neoplatonic.LTR.Nullary
