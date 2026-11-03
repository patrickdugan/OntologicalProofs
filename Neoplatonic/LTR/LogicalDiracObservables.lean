import Neoplatonic.LTR.LogicalLipschitzProjections

/-!
# First-order sentences as bounded-commutator Hilbert projections

On the verified compact-completion spectral triple, every
sentence-truth projection lies in the dense admissible star algebra.
Applying its faithful complex star representation produces a
self-adjoint idempotent bounded operator on the infinite complex
Hilbert space. The bounded-commutator field of the triple applies
to every such named logical operator.

The Hilbert norm-zero test for the *refutation* projection exactly
recovers semantic entailment. The result needs no algorithm
deciding whether a sentence is provable, and does not assert
computability of the compatible Stone metric.
-/

namespace Neoplatonic.LTR

open FirstOrder
open FirstOrder.Language

universe u v w

variable {L : FirstOrder.Language.{u,v}} {T : L.Theory}
variable {α : Type w}
variable [Countable (L.withConstants α).Sentence]

/-- Each sentence truth projection belongs to the actual
chosen logical Stone spectral triple's dense star algebra. -/
theorem logicalSentence_inSpectralObservables
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η)
    (φ : (L.withConstants α).Sentence) :
    letI : MetricSpace (T.CompleteType α) :=
      chosenLogicalStoneMetric (T := T) (α := α)
    complexLogicalProjection (T := T) φ ∈
      (chosenLogicalStoneSpectralTriple hT η hη).observables := by
  letI : MetricSpace (T.CompleteType α) :=
    chosenLogicalStoneMetric (T := T) (α := α)
  change complexLogicalProjection (T := T) φ ∈
    compactComplexLipschitzStarSubalgebra (T.CompleteType α)
  exact complexLogicalProjection_mem_Lipschitz (T := T) (α := α) φ

/-- The actual infinite-Hilbert image of any logical sentence is a
self-adjoint idempotent, hence a concrete orthogonal projection. -/
theorem logicalSentence_HilbertProjection
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η)
    (φ : (L.withConstants α).Sentence) :
    letI : MetricSpace (T.CompleteType α) :=
      chosenLogicalStoneMetric (T := T) (α := α)
    let S := chosenLogicalStoneSpectralTriple hT η hη
    let P := S.representation (complexLogicalProjection (T := T) φ)
    P * P = P ∧ star P = P := by
  letI : MetricSpace (T.CompleteType α) :=
    chosenLogicalStoneMetric (T := T) (α := α)
  let S := chosenLogicalStoneSpectralTriple hT η hη
  let f := complexLogicalProjection (T := T) φ
  constructor
  · change S.representation f * S.representation f = S.representation f
    rw [← map_mul, complexLogicalProjection_idempotent]
  · change star (S.representation f) = S.representation f
    rw [← map_star, complexLogicalProjection_selfadjoint]

/-- The norm of the infinite Hilbert refutation operator is zero
exactly when the underlying sentence is entailed by the theory. -/
theorem logicalSentence_HilbertRefutationNorm_zero_iff
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η)
    (φ : (L.withConstants α).Sentence) :
    letI : MetricSpace (T.CompleteType α) :=
      chosenLogicalStoneMetric (T := T) (α := α)
    ‖(chosenLogicalStoneSpectralTriple hT η hη).representation
      (complexLogicalProjection (T := T) φ.not)‖ = 0 ↔
      (L.lhomWithConstants α).onTheory T ⊨ᵇ φ := by
  letI : MetricSpace (T.CompleteType α) :=
    chosenLogicalStoneMetric (T := T) (α := α)
  let S := chosenLogicalStoneSpectralTriple hT η hη
  let f := complexLogicalProjection (T := T) φ.not
  change ‖S.representation f‖ = 0 ↔
    (L.lhomWithConstants α).onTheory T ⊨ᵇ φ
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

/-- The infinite Dirac commutator of each named truth projection
has a bounded Hilbert extension, on the actual maximal domain. -/
theorem logicalSentence_boundedDiracCommutator
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η)
    (φ : (L.withConstants α).Sentence) :
    letI : MetricSpace (T.CompleteType α) :=
      chosenLogicalStoneMetric (T := T) (α := α)
    let S := chosenLogicalStoneSpectralTriple hT η hη
    ∃ (B : ℝ)
      (C : ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert),
      0 ≤ B ∧ ‖C‖ ≤ B ∧
      ∀ (ψ : ComplexDiracBlockHilbert) (hψ : ψ ∈ S.dirac.domain),
        ∃ hπψ : S.representation (complexLogicalProjection (T := T) φ) ψ ∈
            S.dirac.domain,
          S.dirac ⟨S.representation (complexLogicalProjection (T := T) φ) ψ, hπψ⟩ -
            S.representation (complexLogicalProjection (T := T) φ)
              (S.dirac ⟨ψ, hψ⟩) = C ψ := by
  letI : MetricSpace (T.CompleteType α) :=
    chosenLogicalStoneMetric (T := T) (α := α)
  exact (chosenLogicalStoneSpectralTriple hT η hη).bounded_commutator
    (complexLogicalProjection (T := T) φ)
    (logicalSentence_inSpectralObservables hT η hη φ)

end Neoplatonic.LTR
