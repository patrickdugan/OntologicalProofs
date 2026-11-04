import Neoplatonic.LTR.NullaryEffectiveMetricModulus

/-!
# A fully instantiated first-order spectral triple with encoded syntax

The one-axiom nullary theory has an explicit singleton model,
and its zero-th nullary predicate is independent. Those proofs
eliminate the satisfiability and independence parameters required
by the general numbered logical spectral triple.

Use the constructive full-sentence enumeration from
NullaryEffectiveSyntax to supply the first-disagreement metric.
This constructs a specific complex spectral triple with a faithful
Hilbert representation, self-adjoint infinite Dirac, compact
ordinary resolvent, bounded logical commutators and exact
Connes-style recovery of the numbered metric.

The sentence code and program-modulus lookup are constructive.
A dense sequence of completed theories is still selected
classically, and this Dirac operator is not claimed computable.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.Theory

/-- The concrete one-axiom nullary first-order theory is
satisfiable, witnessed by the explicit all-false singleton model. -/
theorem nullaryTheory_satisfiable : T.IsSatisfiable := by
  have htypes : Nonempty (T.CompleteType Empty) :=
    ⟨encode (fun _ => false)⟩
  exact (CompleteType.nonempty_iff).mp htypes

/-- The zero-th nullary predicate is independent even in the
full empty-constant expansion of the first-order theory. -/
theorem nullaryLiftedAtom_independent :
    Independent T (liftedAtom 0) := by
  apply (independent_iff_nontrivial_locus
    (T := T) (α := Empty) (liftedAtom 0)).mpr
  constructor
  · refine ⟨encode (fun _ => true), ?_⟩
    change liftedAtom 0 ∈ encode (fun _ => true)
    exact (liftedAtom_mem_encode (fun _ => true) 0).mpr (by simp)
  · intro hfull
    have hmem : liftedAtom 0 ∈ encode (fun _ => false) := by
      change (encode (fun _ => false)) ∈ T.typesWith (liftedAtom 0)
      rw [hfull]
      exact Set.mem_univ _
    have hfalse := (liftedAtom_mem_encode (fun _ => false) 0).mp hmem
    simp at hfalse

/-- The concrete compact complex spectral triple of the one-axiom
nullary theory, using the direct natural-number full-sentence code
rather than the classical enumeration of v0.37. -/
noncomputable def effectiveNullaryStoneSpectralTriple :
    letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric effectiveExpandedSentenceCode
        effectiveExpandedSentenceCode_surjective
    CompactComplexSpectralTriple (T.CompleteType Empty) :=
  numberedLogicalStoneSpectralTriple
    effectiveExpandedSentenceCode
    effectiveExpandedSentenceCode_surjective
    nullaryTheory_satisfiable
    (liftedAtom 0)
    nullaryLiftedAtom_independent

end Neoplatonic.LTR.Nullary
