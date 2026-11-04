import Neoplatonic.LTR.NullaryEffectiveSpectralTriple
import Neoplatonic.LTR.LogicalHilbertNormGap

/-!
# Sentence-labelled Hilbert operators on the explicit nullary spectral triple

The concrete one-axiom nullary spectral triple of the previous module
has its metric determined by the constructive complete-syntax numbering.

Every sentence truth projection lies in the admissible Lipschitz
star algebra. Its represented bounded operator is self-adjoint and
idempotent, with a bounded commutator on the true maximal Dirac
domain. The norm of the represented refutation operator vanishes
exactly when that sentence is semantically entailed.

The operator itself uses classical dense-completion witnesses.
The syntax code, its decoder and the sentence-index lookup are
constructive mathematical definitions.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language

/-- Every expanded-language sentence is an admissible observable
of the *specific* syntax-numbered nullary spectral triple. -/
theorem effectiveNullary_sentence_inObservables
    (φ : L[[Empty]].Sentence) :
    letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric effectiveExpandedSentenceCode
        effectiveExpandedSentenceCode_surjective
    complexLogicalProjection (T := T) φ ∈
      effectiveNullaryStoneSpectralTriple.observables := by
  letI : MetricSpace (T.CompleteType Empty) :=
    numberedSentenceMetric effectiveExpandedSentenceCode
      effectiveExpandedSentenceCode_surjective
  change HasFiniteComplexLipschitzConstant
    (complexLogicalProjection (T := T) φ)
  exact compactClopenBinary_finiteLipschitz
    (T.typesWith φ) (locus_isClopen (T := T) (α := Empty) φ)
    (complexLogicalProjection (T := T) φ)
    (fun p hp => complexLogicalProjection_apply_mem
      (T := T) φ p hp)
    (fun p hp => complexLogicalProjection_apply_not_mem
      (T := T) φ p hp)

/-- Every named Hilbert truth operator in the explicitly numbered
triple is a self-adjoint idempotent projection. -/
theorem effectiveNullary_sentence_hilbertProjection
    (φ : L[[Empty]].Sentence) :
    letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric effectiveExpandedSentenceCode
        effectiveExpandedSentenceCode_surjective
    let S := effectiveNullaryStoneSpectralTriple
    let P := S.representation (complexLogicalProjection (T := T) φ)
    P * P = P ∧ star P = P := by
  letI : MetricSpace (T.CompleteType Empty) :=
    numberedSentenceMetric effectiveExpandedSentenceCode
      effectiveExpandedSentenceCode_surjective
  let S := effectiveNullaryStoneSpectralTriple
  let f := complexLogicalProjection (T := T) φ
  constructor
  · change S.representation f * S.representation f = S.representation f
    rw [← map_mul, complexLogicalProjection_idempotent]
  · change star (S.representation f) = S.representation f
    rw [← map_star, complexLogicalProjection_selfadjoint]

/-- The infinite-dimensional Hilbert refutation norm criterion
holds for the explicit syntax-numbered spectral triple. -/
theorem effectiveNullary_refutationNorm_zero_iff_entails
    (φ : L[[Empty]].Sentence) :
    letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric effectiveExpandedSentenceCode
        effectiveExpandedSentenceCode_surjective
    ‖effectiveNullaryStoneSpectralTriple.representation
        (complexLogicalProjection (T := T) φ.not)‖ = 0 ↔
      (L.lhomWithConstants Empty).onTheory T ⊨ᵇ φ := by
  letI : MetricSpace (T.CompleteType Empty) :=
    numberedSentenceMetric effectiveExpandedSentenceCode
      effectiveExpandedSentenceCode_surjective
  let S := effectiveNullaryStoneSpectralTriple
  let f := complexLogicalProjection (T := T) φ.not
  change ‖S.representation f‖ = 0 ↔
    (L.lhomWithConstants Empty).onTheory T ⊨ᵇ φ
  constructor
  · intro hnorm
    have hzero : S.representation f = 0 := norm_eq_zero.mp hnorm
    have hf : f = 0 := S.representation_faithful (by
      simpa only [map_zero] using hzero)
    exact (complex_refutation_norm_zero_iff_entails (T := T) φ).mp
      (norm_eq_zero.mpr hf)
  · intro hent
    have hf : f = 0 := norm_eq_zero.mp
      ((complex_refutation_norm_zero_iff_entails (T := T) φ).mpr hent)
    simp [hf]

/-- Every named sentence projection has a bounded Hilbert Dirac
commutator on the maximal unbounded domain of the actual triple. -/
theorem effectiveNullary_sentence_boundedDiracCommutator
    (φ : L[[Empty]].Sentence) :
    letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric effectiveExpandedSentenceCode
        effectiveExpandedSentenceCode_surjective
    let S := effectiveNullaryStoneSpectralTriple
    ∃ (B : ℝ)
      (C : ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert),
      0 ≤ B ∧ ‖C‖ ≤ B ∧
      ∀ (ψ : ComplexDiracBlockHilbert) (hψ : ψ ∈ S.dirac.domain),
        ∃ hπψ : S.representation (complexLogicalProjection (T := T) φ) ψ ∈
            S.dirac.domain,
          S.dirac ⟨S.representation (complexLogicalProjection (T := T) φ) ψ, hπψ⟩ -
            S.representation (complexLogicalProjection (T := T) φ)
              (S.dirac ⟨ψ, hψ⟩) = C ψ := by
  letI : MetricSpace (T.CompleteType Empty) :=
    numberedSentenceMetric effectiveExpandedSentenceCode
      effectiveExpandedSentenceCode_surjective
  exact effectiveNullaryStoneSpectralTriple.bounded_commutator
    (complexLogicalProjection (T := T) φ)
    (effectiveNullary_sentence_inObservables φ)

end Neoplatonic.LTR.Nullary
