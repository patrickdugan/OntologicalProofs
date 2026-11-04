import Neoplatonic.LTR.NullaryEffectiveQuantitativeOperators

/-!
# Expose the actual dense-pair marking of the syntax-numbered triple

The constructive numbering of expanded nullary sentences defines a
first-disagreement metric on Mathlib's complete-type Stone space.
The infinite Hilbert spectral triple subsequently chooses a
topologically dense sequence of complete types and all ordered
nondegenerate pairs of that sequence.

This module names the selected q, witness indices, and marked
endpoints used by the concrete spectral triple. It verifies coverage
and identifies the existing spectral-triple record with the explicit
dense-pair construction. The enumeration of sentences is constructive;
the dense sequence of completed theories uses classical existence.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.Theory

/-- Classically chosen dense enumeration of actual complete theories,
the same one used inside the numbered spectral-triple constructor. -/
noncomputable abbrev effectiveNullaryDenseSeq :
    ℕ → T.CompleteType Empty :=
  logicalCompleteType_denseSeq (T := T) (α := Empty)
    nullaryTheory_satisfiable

theorem effectiveNullaryDenseSeq_dense :
    DenseRange effectiveNullaryDenseSeq :=
  logicalCompleteType_denseSeq_dense (T := T) (α := Empty)
    nullaryTheory_satisfiable

theorem effectiveNullaryDenseSeq_distinct_exists :
    ∃ a b : ℕ, effectiveNullaryDenseSeq a ≠
      effectiveNullaryDenseSeq b :=
  logicalCompleteType_denseSeq_has_distinct
    (T := T) (α := Empty)
    nullaryTheory_satisfiable (liftedAtom 0)
    nullaryLiftedAtom_independent

/-- The two selected indices used to replace repeated-point
index pairs by a fixed nondegenerate fallback edge. -/
noncomputable def effectiveNullaryDenseMarkA : ℕ :=
  Classical.choose effectiveNullaryDenseSeq_distinct_exists

noncomputable def effectiveNullaryDenseMarkB : ℕ :=
  Classical.choose
    (Classical.choose_spec effectiveNullaryDenseSeq_distinct_exists)

theorem effectiveNullaryDenseMark_distinct :
    effectiveNullaryDenseSeq effectiveNullaryDenseMarkA ≠
      effectiveNullaryDenseSeq effectiveNullaryDenseMarkB :=
  Classical.choose_spec
    (Classical.choose_spec effectiveNullaryDenseSeq_distinct_exists)

/-- Named left and right endpoints of the concrete marked Dirac blocks. -/
noncomputable def effectiveNullaryMarkedLeft : ℕ → T.CompleteType Empty :=
  densePairLeft effectiveNullaryDenseSeq
    effectiveNullaryDenseMarkA effectiveNullaryDenseMarkB

noncomputable def effectiveNullaryMarkedRight : ℕ → T.CompleteType Empty :=
  densePairRight effectiveNullaryDenseSeq
    effectiveNullaryDenseMarkA effectiveNullaryDenseMarkB

theorem effectiveNullaryMarked_distinct :
    ∀ j, effectiveNullaryMarkedLeft j ≠
      effectiveNullaryMarkedRight j :=
  densePair_distinct effectiveNullaryDenseSeq
    effectiveNullaryDenseMarkA effectiveNullaryDenseMarkB
    effectiveNullaryDenseMark_distinct

theorem effectiveNullaryMarked_endpointCover :
    ∀ n, ∃ j, effectiveNullaryMarkedLeft j =
      effectiveNullaryDenseSeq n ∨ effectiveNullaryMarkedRight j =
      effectiveNullaryDenseSeq n :=
  densePair_endpointCover effectiveNullaryDenseSeq
    effectiveNullaryDenseMarkA effectiveNullaryDenseMarkB
    effectiveNullaryDenseMark_distinct

theorem effectiveNullaryMarked_pairCover :
    ∀ m n, effectiveNullaryDenseSeq m ≠ effectiveNullaryDenseSeq n →
      ∃ j, effectiveNullaryMarkedLeft j = effectiveNullaryDenseSeq m ∧
        effectiveNullaryMarkedRight j = effectiveNullaryDenseSeq n :=
  densePair_covers effectiveNullaryDenseSeq
    effectiveNullaryDenseMarkA effectiveNullaryDenseMarkB

/-- The previously built concrete spectral-triple record is exactly
the dense-pair constructor at the named selected endpoints. -/
theorem effectiveNullaryStoneSpectralTriple_eq_explicit :
    letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric effectiveExpandedSentenceCode
        effectiveExpandedSentenceCode_surjective
    effectiveNullaryStoneSpectralTriple =
      explicitDensePairSpectralTriple effectiveNullaryDenseSeq
        effectiveNullaryDenseSeq_dense
        effectiveNullaryDenseMarkA effectiveNullaryDenseMarkB
        effectiveNullaryDenseMark_distinct := by
  rfl

end Neoplatonic.LTR.Nullary
