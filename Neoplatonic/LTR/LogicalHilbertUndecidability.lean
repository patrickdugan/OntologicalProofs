import Neoplatonic.LTR.LogicalSyntacticHilbertPullback
import Neoplatonic.LTR.EffectiveSpectral

/-!
# Effective obstruction for sentence-labelled Hilbert operator norms

A natural-number code names a first-order sentence and hence a
bounded self-adjoint idempotent on the actual infinite complex
Hilbert space of the chosen logical Stone spectral triple.

The question whether the norm of its *refutation* operator vanishes
is identical, code for code, to the original semantic entailment
predicate. The same-code many-one reduction and exact equivalence
of computability are proved.

A semantic-undecidability input is an explicit hypothesis.
This module does not assume an algorithm that constructs completed
theories, selected metrics, or Hilbert operators from sentence codes.
-/

namespace Neoplatonic.LTR

open FirstOrder
open FirstOrder.Language

universe u v w

variable {L : FirstOrder.Language.{u,v}} {T : L.Theory} {α : Type w}
variable [Countable (L.withConstants α).Sentence]

/-- The concrete infinite-dimensional Hilbert refutation norm
vanishes exactly when the corresponding sentence is entailed. -/
theorem logicalHilbertRefutationNorm_zero_iff_entails
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η)
    (φ : (L.withConstants α).Sentence) :
    ‖logicalSentenceHilbertOp hT η hη φ.not‖ = 0 ↔
      (L.lhomWithConstants α).onTheory T ⊨ᵇ φ := by
  simpa only [logicalSentenceHilbertOp] using
    (logicalSentence_HilbertRefutationNorm_zero_iff hT η hη φ)

/-- An identity many-one reduction sends semantic entailment to
the norm-zero test for its named Hilbert refutation operator. -/
theorem entailment_manyOneReducible_HilbertRefutationNorm
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η)
    (code : ℕ → (L.withConstants α).Sentence) :
    ManyOneReducible
      (fun n => (L.lhomWithConstants α).onTheory T ⊨ᵇ code n)
      (fun n => ‖logicalSentenceHilbertOp hT η hη (code n).not‖ = 0) := by
  refine ⟨id, Computable.id, ?_⟩
  intro n
  exact (logicalHilbertRefutationNorm_zero_iff_entails
    hT η hη (code n)).symm

/-- The computability of the concrete infinite Hilbert refutation
norm-zero predicate is equivalent to computability of entailment. -/
theorem logicalHilbertRefutationNorm_computable_iff_entailment
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η)
    (code : ℕ → (L.withConstants α).Sentence) :
    ComputablePred
      (fun n => ‖logicalSentenceHilbertOp hT η hη (code n).not‖ = 0) ↔
    ComputablePred
      (fun n => (L.lhomWithConstants α).onTheory T ⊨ᵇ code n) := by
  have heq :
      (fun n => ‖logicalSentenceHilbertOp hT η hη (code n).not‖ = 0) =
      (fun n => (L.lhomWithConstants α).onTheory T ⊨ᵇ code n) := by
    funext n
    exact propext
      (logicalHilbertRefutationNorm_zero_iff_entails hT η hη (code n))
  rw [heq]

/-- Undecidability of semantic entailment transfers to norm-zero
testing on the actual Hilbert-space Dirac representation. -/
theorem logicalHilbertRefutationNorm_undecidable_of_entailment
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η)
    (code : ℕ → (L.withConstants α).Sentence)
    (h : ¬ ComputablePred
      (fun n => (L.lhomWithConstants α).onTheory T ⊨ᵇ code n)) :
    ¬ ComputablePred
      (fun n => ‖logicalSentenceHilbertOp hT η hη (code n).not‖ = 0) := by
  intro hc
  exact h
    ((logicalHilbertRefutationNorm_computable_iff_entailment
      hT η hη code).mp hc)

end Neoplatonic.LTR
