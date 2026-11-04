import Neoplatonic.LTR.LogicalBooleanOperators
import Neoplatonic.LTR.LogicalPullback

/-!
# Syntactic translation of logical Hilbert projections

The verified nullary one-axiom first-order theory has a syntactic
predicate renaming for each partial-recursive code. Its induced
continuous map of the completed-type Stone space commutes with
pullback of *every* original-language sentence truth projection.

Complexification transports this commuting square into C(X, ℂ).
For the chosen logical Stone spectral triple, applying the
Hilbert star representation then identifies the pulled-back
operator exactly with the Hilbert projection of the renamed
sentence. The pulled-back observable belongs to the dense
Lipschitz algebra and therefore has a bounded Dirac commutator.

No Hilbert-space intertwiner for the Dirac operators is asserted:
the syntactic maps may have unbounded metric distortion.
-/

namespace Neoplatonic.LTR

open FirstOrder
open FirstOrder.Language

/-- Syntactic renaming and pullback commute for complex-valued
continuous first-order truth observables. -/
theorem complexLogicalProjection_syntax_pullback
    (e : Nat.Partrec.Code) (φ : Nullary.L.Sentence) :
    (complexLogicalProjection (T := Nullary.T)
        (Nullary.liftedSentence φ)).comp (syntaxMapContinuous e) =
      complexLogicalProjection (T := Nullary.T)
        (Nullary.liftedSentence
          ((Nullary.haltingRename e).onSentence φ)) := by
  ext p
  have hreal := congrArg
    (fun f : C(Nullary.T.CompleteType Empty, ℝ) => f p)
    (logicalProjection_syntax_pullback e φ)
  have hcomplex := congrArg (fun z : ℝ => (z : ℂ)) hreal
  change
    ((logicalProjection (T := Nullary.T) (Nullary.liftedSentence φ)
        (syntaxMapContinuous e p) : ℝ) : ℂ) =
      ((logicalProjection (T := Nullary.T)
          (Nullary.liftedSentence
            ((Nullary.haltingRename e).onSentence φ)) p : ℝ) : ℂ)
  simpa only [ContinuousMap.comp_apply] using hcomplex

variable [Countable (Nullary.L.withConstants Empty).Sentence]

/-- The pullback of each named nullary-language truth projection
is a valid Lipschitz observable of the chosen spectral triple,
even for syntactic maps with unbounded metric distortion. -/
theorem syntaxPullback_inSpectralObservables
    (hT : Nullary.T.IsSatisfiable)
    (η : (Nullary.L.withConstants Empty).Sentence)
    (hη : Independent Nullary.T η)
    (e : Nat.Partrec.Code) (φ : Nullary.L.Sentence) :
    letI : MetricSpace (Nullary.T.CompleteType Empty) :=
      chosenLogicalStoneMetric (T := Nullary.T) (α := Empty)
    (complexLogicalProjection (T := Nullary.T)
      (Nullary.liftedSentence φ)).comp (syntaxMapContinuous e) ∈
        (chosenLogicalStoneSpectralTriple hT η hη).observables := by
  letI : MetricSpace (Nullary.T.CompleteType Empty) :=
    chosenLogicalStoneMetric (T := Nullary.T) (α := Empty)
  rw [complexLogicalProjection_syntax_pullback]
  exact logicalSentence_inSpectralObservables hT η hη
    (Nullary.liftedSentence ((Nullary.haltingRename e).onSentence φ))

/-- The Hilbert operator representing a syntactically pulled-back
sentence projection is exactly the represented renamed sentence. -/
theorem syntaxPullback_HilbertProjection
    (hT : Nullary.T.IsSatisfiable)
    (η : (Nullary.L.withConstants Empty).Sentence)
    (hη : Independent Nullary.T η)
    (e : Nat.Partrec.Code) (φ : Nullary.L.Sentence) :
    letI : MetricSpace (Nullary.T.CompleteType Empty) :=
      chosenLogicalStoneMetric (T := Nullary.T) (α := Empty)
    (chosenLogicalStoneSpectralTriple hT η hη).representation
      ((complexLogicalProjection (T := Nullary.T)
        (Nullary.liftedSentence φ)).comp (syntaxMapContinuous e)) =
      logicalSentenceHilbertOp hT η hη
        (Nullary.liftedSentence
          ((Nullary.haltingRename e).onSentence φ)) := by
  letI : MetricSpace (Nullary.T.CompleteType Empty) :=
    chosenLogicalStoneMetric (T := Nullary.T) (α := Empty)
  rw [complexLogicalProjection_syntax_pullback]

/-- The actual infinite unbounded Dirac commutator with the
syntactically pulled-back truth projection has a bounded extension. -/
theorem syntaxPullback_boundedDiracCommutator
    (hT : Nullary.T.IsSatisfiable)
    (η : (Nullary.L.withConstants Empty).Sentence)
    (hη : Independent Nullary.T η)
    (e : Nat.Partrec.Code) (φ : Nullary.L.Sentence) :
    letI : MetricSpace (Nullary.T.CompleteType Empty) :=
      chosenLogicalStoneMetric (T := Nullary.T) (α := Empty)
    let S := chosenLogicalStoneSpectralTriple hT η hη
    let f := (complexLogicalProjection (T := Nullary.T)
      (Nullary.liftedSentence φ)).comp (syntaxMapContinuous e)
    ∃ (B : ℝ)
      (C : ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert),
      0 ≤ B ∧ ‖C‖ ≤ B ∧
      ∀ (ψ : ComplexDiracBlockHilbert) (hψ : ψ ∈ S.dirac.domain),
        ∃ hπψ : S.representation f ψ ∈ S.dirac.domain,
          S.dirac ⟨S.representation f ψ, hπψ⟩ -
            S.representation f (S.dirac ⟨ψ, hψ⟩) = C ψ := by
  letI : MetricSpace (Nullary.T.CompleteType Empty) :=
    chosenLogicalStoneMetric (T := Nullary.T) (α := Empty)
  exact (chosenLogicalStoneSpectralTriple hT η hη).bounded_commutator _
    (syntaxPullback_inSpectralObservables hT η hη e φ)

end Neoplatonic.LTR
