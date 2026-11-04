import Neoplatonic.LTR.LogicalDiracObservables

/-!
# Boolean sentence algebra represented on the infinite Dirac Hilbert space

The pointwise characteristic functions of first-order sentence
truth loci preserve Boolean conjunction and complement.
Applying the faithful complex star-algebra representation yields
genuine orthogonal Hilbert projections whose multiplication
encodes the logical meet, and whose complement encodes negation.

Equality of represented operators exactly detects equality of
the labelled clopen truth loci. Projection absorption is equivalent
to semantic containment of truth loci.

The theorems concern the concrete complex Hilbert operator
representation from the chosen logical Stone spectral triple.
-/

namespace Neoplatonic.LTR

open FirstOrder Set
open FirstOrder.Language
open FirstOrder.Language.Theory

universe u v w

variable {L : FirstOrder.Language.{u,v}} {T : L.Theory} {α : Type w}

/-- Boolean complement becomes subtraction from the unit in
the complex continuous-function algebra of logical completions. -/
theorem complexLogicalProjection_not
    (φ : (L.withConstants α).Sentence) :
    complexLogicalProjection (T := T) φ.not =
      1 - complexLogicalProjection (T := T) φ := by
  ext p
  change complexLogicalProjection (T := T) φ.not p =
    1 - complexLogicalProjection (T := T) φ p
  by_cases hp : φ ∈ p
  · have hn : φ.not ∉ p := by
      intro hh
      exact (p.not_mem_iff φ).mp hh hp
    rw [complexLogicalProjection_apply_not_mem (T := T) φ.not p hn,
      complexLogicalProjection_apply_mem (T := T) φ p hp]
    norm_num
  · have hn : φ.not ∈ p := (p.not_mem_iff φ).mpr hp
    rw [complexLogicalProjection_apply_mem (T := T) φ.not p hn,
      complexLogicalProjection_apply_not_mem (T := T) φ p hp]
    norm_num

/-- The intersection of two sentence truth loci is represented
by pointwise multiplication of their complex characteristic functions. -/
theorem complexLogicalProjection_inf
    (φ ψ : (L.withConstants α).Sentence) :
    complexLogicalProjection (T := T) (φ ⊓ ψ) =
      complexLogicalProjection (T := T) φ *
        complexLogicalProjection (T := T) ψ := by
  ext p
  change complexLogicalProjection (T := T) (φ ⊓ ψ) p =
    complexLogicalProjection (T := T) φ p *
      complexLogicalProjection (T := T) ψ p
  have hmem : (φ ⊓ ψ) ∈ p ↔ φ ∈ p ∧ ψ ∈ p := by
    change p ∈ T.typesWith (φ ⊓ ψ) ↔
      p ∈ T.typesWith φ ∩ T.typesWith ψ
    rw [CompleteType.typesWith_inf]
    rfl
  by_cases hp : φ ∈ p
  · by_cases hq : ψ ∈ p
    · have hboth : (φ ⊓ ψ) ∈ p := hmem.mpr ⟨hp, hq⟩
      rw [complexLogicalProjection_apply_mem (T := T) (φ ⊓ ψ) p hboth,
        complexLogicalProjection_apply_mem (T := T) φ p hp,
        complexLogicalProjection_apply_mem (T := T) ψ p hq]
      norm_num
    · have hno : (φ ⊓ ψ) ∉ p := fun h => hq (hmem.mp h).2
      rw [complexLogicalProjection_apply_not_mem (T := T) (φ ⊓ ψ) p hno,
        complexLogicalProjection_apply_mem (T := T) φ p hp,
        complexLogicalProjection_apply_not_mem (T := T) ψ p hq]
      norm_num
  · by_cases hq : ψ ∈ p
    · have hno : (φ ⊓ ψ) ∉ p := fun h => hp (hmem.mp h).1
      rw [complexLogicalProjection_apply_not_mem (T := T) (φ ⊓ ψ) p hno,
        complexLogicalProjection_apply_not_mem (T := T) φ p hp,
        complexLogicalProjection_apply_mem (T := T) ψ p hq]
      norm_num
    · have hno : (φ ⊓ ψ) ∉ p := fun h => hp (hmem.mp h).1
      rw [complexLogicalProjection_apply_not_mem (T := T) (φ ⊓ ψ) p hno,
        complexLogicalProjection_apply_not_mem (T := T) φ p hp,
        complexLogicalProjection_apply_not_mem (T := T) ψ p hq]
      norm_num

/-- Two named complex logical observables are equal exactly when
their sentence-truth loci are equal as subsets of completion space. -/
theorem complexLogicalProjection_eq_iff_locus
    (φ ψ : (L.withConstants α).Sentence) :
    complexLogicalProjection (T := T) φ =
      complexLogicalProjection (T := T) ψ ↔
    T.typesWith φ = T.typesWith ψ := by
  constructor
  · intro heq
    ext p
    constructor
    · intro hp
      by_contra hq
      have hv := congrArg
        (fun f : C(T.CompleteType α, ℂ) => f p) heq
      rw [complexLogicalProjection_apply_mem (T := T) φ p hp,
        complexLogicalProjection_apply_not_mem (T := T) ψ p hq] at hv
      norm_num at hv
    · intro hq
      by_contra hp
      have hv := congrArg
        (fun f : C(T.CompleteType α, ℂ) => f p) heq
      rw [complexLogicalProjection_apply_not_mem (T := T) φ p hp,
        complexLogicalProjection_apply_mem (T := T) ψ p hq] at hv
      norm_num at hv
  · intro heq
    ext p
    by_cases hp : φ ∈ p
    · have hq : ψ ∈ p := by
        have hmem : p ∈ T.typesWith φ := hp
        rw [heq] at hmem
        exact hmem
      rw [complexLogicalProjection_apply_mem (T := T) φ p hp,
        complexLogicalProjection_apply_mem (T := T) ψ p hq]
    · have hq : ψ ∉ p := by
        intro hq
        apply hp
        have hmem : p ∈ T.typesWith ψ := hq
        rw [← heq] at hmem
        exact hmem
      rw [complexLogicalProjection_apply_not_mem (T := T) φ p hp,
        complexLogicalProjection_apply_not_mem (T := T) ψ p hq]

variable [Countable (L.withConstants α).Sentence]

/-- The actual bounded Hilbert operator representing the truth of
a named sentence in the classically chosen Stone spectral triple. -/
noncomputable abbrev logicalSentenceHilbertOp
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η)
    (φ : (L.withConstants α).Sentence) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  letI : MetricSpace (T.CompleteType α) :=
    chosenLogicalStoneMetric (T := T) (α := α)
  (chosenLogicalStoneSpectralTriple hT η hη).representation
    (complexLogicalProjection (T := T) φ)

/-- Logical negation is represented by the Hilbert projection
complement, inside the genuine bounded operator algebra. -/
theorem logicalSentenceHilbertOp_not
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η)
    (φ : (L.withConstants α).Sentence) :
    logicalSentenceHilbertOp hT η hη φ.not =
      1 - logicalSentenceHilbertOp hT η hη φ := by
  letI : MetricSpace (T.CompleteType α) :=
    chosenLogicalStoneMetric (T := T) (α := α)
  let S := chosenLogicalStoneSpectralTriple hT η hη
  change S.representation (complexLogicalProjection (T := T) φ.not) =
    1 - S.representation (complexLogicalProjection (T := T) φ)
  rw [complexLogicalProjection_not, map_sub, map_one]

/-- The Hilbert product of truth projections is exactly the
projection of the syntactic conjunction. -/
theorem logicalSentenceHilbertOp_inf
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η)
    (φ ψ : (L.withConstants α).Sentence) :
    logicalSentenceHilbertOp hT η hη (φ ⊓ ψ) =
      logicalSentenceHilbertOp hT η hη φ *
        logicalSentenceHilbertOp hT η hη ψ := by
  letI : MetricSpace (T.CompleteType α) :=
    chosenLogicalStoneMetric (T := T) (α := α)
  let S := chosenLogicalStoneSpectralTriple hT η hη
  change S.representation (complexLogicalProjection (T := T) (φ ⊓ ψ)) =
    S.representation (complexLogicalProjection (T := T) φ) *
      S.representation (complexLogicalProjection (T := T) ψ)
  rw [complexLogicalProjection_inf, map_mul]

/-- Equality of the represented operators detects equality of
labelled clopens; the representation is faithful on all of C(X). -/
theorem logicalSentenceHilbertOp_eq_iff_locus
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η)
    (φ ψ : (L.withConstants α).Sentence) :
    logicalSentenceHilbertOp hT η hη φ =
      logicalSentenceHilbertOp hT η hη ψ ↔
    T.typesWith φ = T.typesWith ψ := by
  letI : MetricSpace (T.CompleteType α) :=
    chosenLogicalStoneMetric (T := T) (α := α)
  let S := chosenLogicalStoneSpectralTriple hT η hη
  change S.representation (complexLogicalProjection (T := T) φ) =
    S.representation (complexLogicalProjection (T := T) ψ) ↔
      T.typesWith φ = T.typesWith ψ
  exact S.representation_faithful.eq_iff.trans
    (complexLogicalProjection_eq_iff_locus φ ψ)

/-- Absorption of sentence projections encodes the inclusion
order on the labelled clopen truth loci. -/
theorem logicalSentenceHilbertOp_mul_eq_self_iff_subset
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η)
    (φ ψ : (L.withConstants α).Sentence) :
    logicalSentenceHilbertOp hT η hη φ *
      logicalSentenceHilbertOp hT η hη ψ =
      logicalSentenceHilbertOp hT η hη φ ↔
    T.typesWith φ ⊆ T.typesWith ψ := by
  rw [← logicalSentenceHilbertOp_inf]
  rw [logicalSentenceHilbertOp_eq_iff_locus]
  rw [CompleteType.typesWith_inf]
  constructor
  · intro h p hp
    have hp' : p ∈ T.typesWith φ ∩ T.typesWith ψ := by
      rw [h]
      exact hp
    exact hp'.2
  · intro h
    apply Set.Subset.antisymm Set.inter_subset_left
    intro p hp
    exact ⟨hp, h hp⟩

end Neoplatonic.LTR
