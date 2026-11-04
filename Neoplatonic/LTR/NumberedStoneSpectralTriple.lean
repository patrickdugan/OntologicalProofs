import Neoplatonic.LTR.NumberedSentenceMetric

/-!
# A first-order spectral triple using the numbered-sentence metric

Replace the abstract Urysohn metric of the earlier logical Stone
construction by the exact first-disagreement metric induced by a
surjective sentence numbering. Its topology is the original Stone
topology, so the existing classically selected dense sequence remains
dense and the explicit ordered-pair marking is available.

The resulting faithful complex spectral triple retains the entire
compact-resolvent, self-adjointness, bounded-commutator and Connes-style
metric recovery machinery. Its metric is tied to the sentence numbering.

For a countable sentence type we also select a surjective numbering
classically. This selection is an existence result and should not
be mistaken for a computable syntax decoder.
-/

namespace Neoplatonic.LTR

open FirstOrder Set TopologicalSpace
open FirstOrder.Language.Theory

universe u v w

variable {L : FirstOrder.Language.{u,v}} {T : L.Theory} {α : Type w}

/-- A countable first-order sentence type has a classical surjective
enumeration by natural numbers; duplicates are allowed. -/
noncomputable def classicalSentenceNumbering
    [Countable (L.withConstants α).Sentence] :
    ℕ → (L.withConstants α).Sentence := by
  letI : Nonempty (L.withConstants α).Sentence := ⟨⊤⟩
  exact Classical.choose
    (exists_surjective_nat (L.withConstants α).Sentence)

/-- Every expanded-language sentence occurs in the chosen numbering. -/
theorem classicalSentenceNumbering_surjective
    [Countable (L.withConstants α).Sentence] :
    Function.Surjective
      (classicalSentenceNumbering (L := L) (α := α)) := by
  letI : Nonempty (L.withConstants α).Sentence := ⟨⊤⟩
  exact Classical.choose_spec
    (exists_surjective_nat (L.withConstants α).Sentence)

/-- A compact complex spectral triple whose Connes-style dual metric
is determined by a supplied surjective sentence enumeration. -/
noncomputable def numberedLogicalStoneSpectralTriple
    [Countable (L.withConstants α).Sentence]
    (code : ℕ → (L.withConstants α).Sentence)
    (hcode : Function.Surjective code)
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η) :
    letI : MetricSpace (T.CompleteType α) :=
      numberedSentenceMetric code hcode
    CompactComplexSpectralTriple (T.CompleteType α) := by
  letI : MetricSpace (T.CompleteType α) :=
    numberedSentenceMetric code hcode
  letI : SecondCountableTopology (T.CompleteType α) :=
    logicalCompleteType_secondCountable (T := T) (α := α)
  letI : Nonempty (T.CompleteType α) :=
    (CompleteType.nonempty_iff).mpr hT
  let q : ℕ → T.CompleteType α :=
    logicalCompleteType_denseSeq (T := T) (α := α) hT
  have hq : DenseRange q :=
    logicalCompleteType_denseSeq_dense (T := T) (α := α) hT
  have htwo : ∃ a b : ℕ, q a ≠ q b :=
    logicalCompleteType_denseSeq_has_distinct
      (T := T) (α := α) hT η hη
  let a : ℕ := Classical.choose htwo
  let b : ℕ := Classical.choose (Classical.choose_spec htwo)
  have hab : q a ≠ q b :=
    Classical.choose_spec (Classical.choose_spec htwo)
  exact explicitDensePairSpectralTriple q hq a b hab

/-- Without an externally chosen numbering, a countable
sentence language supplies a classically selected one. The
selected metric is still defined by first sentence disagreement. -/
noncomputable def classicalSentenceStoneSpectralTriple
    [Countable (L.withConstants α).Sentence]
    (hT : T.IsSatisfiable)
    (η : (L.withConstants α).Sentence)
    (hη : Independent T η) :
    letI : MetricSpace (T.CompleteType α) :=
      numberedSentenceMetric
        (classicalSentenceNumbering (L := L) (α := α))
        (classicalSentenceNumbering_surjective (L := L) (α := α))
    CompactComplexSpectralTriple (T.CompleteType α) :=
  numberedLogicalStoneSpectralTriple
    (classicalSentenceNumbering (L := L) (α := α))
    (classicalSentenceNumbering_surjective (L := L) (α := α))
    hT η hη

end Neoplatonic.LTR
