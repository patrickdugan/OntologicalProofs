import Neoplatonic.LTR.NullaryEffectiveHilbertOperators
import Neoplatonic.LTR.LogicalSyntacticHilbertPullback

/-!
# The concrete syntax-numbered Hilbert algebra respects logical translations

The one-axiom nullary theory has a faithful complex Hilbert
representation on its actual complete-type Stone space, with a
sentence-numbered first-disagreement metric.

All expanded-language sentence projections obey Boolean identities
inside that representation. For every partial-recursive code, the
actual language endomorphism acts contravariantly on those projections:
the pullback of a named truth projection is precisely the projection
of the syntactically renamed full first-order sentence.

The pullback is a valid Lipschitz observable in the *specific*
syntax-numbered spectral triple. Its commutator with the maximal
self-adjoint Dirac therefore has a bounded Hilbert extension.

These identities concern the represented sentence algebra. They
do not supply a unitary operator intertwining the Dirac itself.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language

/-- The actual bounded operator representing a named expanded
sentence in the concrete syntax-numbered spectral triple. -/
noncomputable abbrev effectiveNullaryHilbertOp
    (φ : L[[Empty]].Sentence) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  letI : MetricSpace (T.CompleteType Empty) :=
    numberedSentenceMetric effectiveExpandedSentenceCode
      effectiveExpandedSentenceCode_surjective
  effectiveNullaryStoneSpectralTriple.representation
    (complexLogicalProjection (T := T) φ)

/-- Logical negation is a complementary Hilbert projection in the
actual concrete numbered Stone spectral triple. -/
theorem effectiveNullaryHilbertOp_not
    (φ : L[[Empty]].Sentence) :
    effectiveNullaryHilbertOp φ.not =
      1 - effectiveNullaryHilbertOp φ := by
  letI : MetricSpace (T.CompleteType Empty) :=
    numberedSentenceMetric effectiveExpandedSentenceCode
      effectiveExpandedSentenceCode_surjective
  let S := effectiveNullaryStoneSpectralTriple
  change S.representation (complexLogicalProjection (T := T) φ.not) =
    1 - S.representation (complexLogicalProjection (T := T) φ)
  rw [complexLogicalProjection_not, map_sub, map_one]

/-- The conjunction of named truth conditions is represented by
the product of their bounded complex Hilbert projections. -/
theorem effectiveNullaryHilbertOp_inf
    (φ ψ : L[[Empty]].Sentence) :
    effectiveNullaryHilbertOp (φ ⊓ ψ) =
      effectiveNullaryHilbertOp φ * effectiveNullaryHilbertOp ψ := by
  letI : MetricSpace (T.CompleteType Empty) :=
    numberedSentenceMetric effectiveExpandedSentenceCode
      effectiveExpandedSentenceCode_surjective
  let S := effectiveNullaryStoneSpectralTriple
  change S.representation (complexLogicalProjection (T := T) (φ ⊓ ψ)) =
    S.representation (complexLogicalProjection (T := T) φ) *
      S.representation (complexLogicalProjection (T := T) ψ)
  rw [complexLogicalProjection_inf, map_mul]

/-- Equality of the actual concrete Hilbert operators is equivalent
to equality of the two sentence-truth loci in complete-type space. -/
theorem effectiveNullaryHilbertOp_eq_iff_locus
    (φ ψ : L[[Empty]].Sentence) :
    effectiveNullaryHilbertOp φ = effectiveNullaryHilbertOp ψ ↔
      T.typesWith φ = T.typesWith ψ := by
  letI : MetricSpace (T.CompleteType Empty) :=
    numberedSentenceMetric effectiveExpandedSentenceCode
      effectiveExpandedSentenceCode_surjective
  let S := effectiveNullaryStoneSpectralTriple
  change S.representation (complexLogicalProjection (T := T) φ) =
    S.representation (complexLogicalProjection (T := T) ψ) ↔
      T.typesWith φ = T.typesWith ψ
  exact S.representation_faithful.eq_iff.trans
    (complexLogicalProjection_eq_iff_locus φ ψ)

/-- Full first-order sentence translation commutes with pullback of
complex truth projections along the concrete complete-type map. -/
theorem effectiveNullary_complexProjection_syntaxPullback
    (e : Nat.Partrec.Code) (φ : L[[Empty]].Sentence) :
    (complexLogicalProjection (T := T) φ).comp
      (syntaxMapContinuous e) =
    complexLogicalProjection (T := T)
      (expandedHaltingRename e φ) := by
  simpa only [expandedHaltingRename, lift_unliftExpandedSentence] using
    (complexLogicalProjection_syntax_pullback e
      (unliftExpandedSentence φ))

/-- The Hilbert representation of a syntactic pullback is exactly
the represented projection of the renamed expanded sentence. -/
theorem effectiveNullaryHilbertOp_syntaxPullback
    (e : Nat.Partrec.Code) (φ : L[[Empty]].Sentence) :
    letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric effectiveExpandedSentenceCode
        effectiveExpandedSentenceCode_surjective
    effectiveNullaryStoneSpectralTriple.representation
      ((complexLogicalProjection (T := T) φ).comp
        (syntaxMapContinuous e)) =
      effectiveNullaryHilbertOp (expandedHaltingRename e φ) := by
  letI : MetricSpace (T.CompleteType Empty) :=
    numberedSentenceMetric effectiveExpandedSentenceCode
      effectiveExpandedSentenceCode_surjective
  change effectiveNullaryStoneSpectralTriple.representation
      ((complexLogicalProjection (T := T) φ).comp
        (syntaxMapContinuous e)) =
    effectiveNullaryStoneSpectralTriple.representation
      (complexLogicalProjection (T := T) (expandedHaltingRename e φ))
  rw [effectiveNullary_complexProjection_syntaxPullback]

/-- Every named sentence projection pulled back by an actual nullary
syntax map remains admissible in the concrete spectral triple. -/
theorem effectiveNullary_syntaxPullback_inObservables
    (e : Nat.Partrec.Code) (φ : L[[Empty]].Sentence) :
    letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric effectiveExpandedSentenceCode
        effectiveExpandedSentenceCode_surjective
    (complexLogicalProjection (T := T) φ).comp
      (syntaxMapContinuous e) ∈
      effectiveNullaryStoneSpectralTriple.observables := by
  letI : MetricSpace (T.CompleteType Empty) :=
    numberedSentenceMetric effectiveExpandedSentenceCode
      effectiveExpandedSentenceCode_surjective
  rw [effectiveNullary_complexProjection_syntaxPullback]
  exact effectiveNullary_sentence_inObservables
    (expandedHaltingRename e φ)

/-- The genuine unbounded Dirac commutator of every syntactically
pulled-back sentence projection extends to a bounded complex
Hilbert operator on the concrete syntax-numbered spectral triple. -/
theorem effectiveNullary_syntaxPullback_boundedDiracCommutator
    (e : Nat.Partrec.Code) (φ : L[[Empty]].Sentence) :
    letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric effectiveExpandedSentenceCode
        effectiveExpandedSentenceCode_surjective
    let S := effectiveNullaryStoneSpectralTriple
    let f := (complexLogicalProjection (T := T) φ).comp
      (syntaxMapContinuous e)
    ∃ (B : ℝ)
      (C : ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert),
      0 ≤ B ∧ ‖C‖ ≤ B ∧
      ∀ (ψ : ComplexDiracBlockHilbert) (hψ : ψ ∈ S.dirac.domain),
        ∃ hπψ : S.representation f ψ ∈ S.dirac.domain,
          S.dirac ⟨S.representation f ψ, hπψ⟩ -
            S.representation f (S.dirac ⟨ψ, hψ⟩) = C ψ := by
  letI : MetricSpace (T.CompleteType Empty) :=
    numberedSentenceMetric effectiveExpandedSentenceCode
      effectiveExpandedSentenceCode_surjective
  exact effectiveNullaryStoneSpectralTriple.bounded_commutator
    ((complexLogicalProjection (T := T) φ).comp
      (syntaxMapContinuous e))
    (effectiveNullary_syntaxPullback_inObservables e φ)

end Neoplatonic.LTR.Nullary
