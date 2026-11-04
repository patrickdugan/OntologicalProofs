import Neoplatonic.LTR.NullaryEffectiveOperatorPullback

/-!
# Explicit finite bounds for syntactically translated Dirac observables

For the concrete one-axiom nullary first-order theory, the complete
expanded-language sentence enumeration has a direct natural-number
encoding. A partial-recursive program e induces a total index lookup

  k_e(j) = encode (rename_e (decode (j))).

The syntactic pullback of the j-th sentence projection is the truth
projection of the sentence numbered k_e(j). By the verified
first-disagreement metric calculation, this projection is
2^(k_e(j))-Lipschitz, with a marked infinite-dimensional Hilbert
commutator norm bounded by the same explicit number.

All results are about *named sentence projections*. They do not
assert a finite global Lipschitz constant for the entire map F_e.
The selected Dirac uses classical dense completion witnesses, and
the numerical upper bound may be exponentially large.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language

/-- The pullback of the j-th coded sentence projection equals
the projection of the directly encoded translated sentence. -/
theorem effectiveNullary_codedProjection_pullback
    (e : Nat.Partrec.Code) (j : ℕ) :
    (complexLogicalProjection (T := T)
      (effectiveExpandedSentenceCode j)).comp
        (syntaxMapContinuous e) =
      complexLogicalProjection (T := T)
        (effectiveExpandedSentenceCode
          (effectiveHaltingSentenceLookup e j)) := by
  rw [effectiveNullary_complexProjection_syntaxPullback,
    effectiveHaltingSentenceLookup_spec]

/-- For the full syntax-numbered Stone metric, the pullback of
the j-th coded sentence truth projection has explicit Lipschitz
constant at most 2^(k_e(j)). -/
theorem effectiveNullary_codedPullback_lipschitz
    (e : Nat.Partrec.Code) (j : ℕ) :
    letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric effectiveExpandedSentenceCode
        effectiveExpandedSentenceCode_surjective
    ∀ p q : T.CompleteType Empty,
      ‖((complexLogicalProjection (T := T)
        (effectiveExpandedSentenceCode j)).comp
          (syntaxMapContinuous e)) p -
        ((complexLogicalProjection (T := T)
          (effectiveExpandedSentenceCode j)).comp
            (syntaxMapContinuous e)) q‖ ≤
        (2 : ℝ)^(effectiveHaltingSentenceLookup e j) * dist p q := by
  letI : MetricSpace (T.CompleteType Empty) :=
    numberedSentenceMetric effectiveExpandedSentenceCode
      effectiveExpandedSentenceCode_surjective
  rw [effectiveNullary_codedProjection_pullback]
  exact numberedSentenceProjection_lipschitz
    (T := T) effectiveExpandedSentenceCode
    effectiveExpandedSentenceCode_surjective
    (effectiveHaltingSentenceLookup e j)

/-- A direct bound on the actual bounded complex Hilbert
marked-edge commutator of each named syntactic pullback, for
arbitrary nondegenerate marked edges and any diagonal masses. -/
theorem effectiveNullary_codedPullback_commutator_norm_le
    (e : Nat.Partrec.Code) (j : ℕ)
    (left right : ℕ → T.CompleteType Empty)
    (hdistinct : ∀ n, left n ≠ right n)
    (mass : ℕ → ℝ) :
    letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric effectiveExpandedSentenceCode
        effectiveExpandedSentenceCode_surjective
    let f := (complexLogicalProjection (T := T)
      (effectiveExpandedSentenceCode j)).comp (syntaxMapContinuous e)
    ∃ (hEdge : ∀ n,
      |(dist (left n) (right n))⁻¹| *
        ‖f (right n) - f (left n)‖ ≤
        (2 : ℝ)^(effectiveHaltingSentenceLookup e j)),
      ‖complexValuedPairCommutatorCLM
          mass
          (fun n => (dist (left n) (right n))⁻¹)
          (fun n => f (left n)) (fun n => f (right n))
          ((2 : ℝ)^(effectiveHaltingSentenceLookup e j))
          (by positivity) hEdge‖ ≤
        (2 : ℝ)^(effectiveHaltingSentenceLookup e j) := by
  letI : MetricSpace (T.CompleteType Empty) :=
    numberedSentenceMetric effectiveExpandedSentenceCode
      effectiveExpandedSentenceCode_surjective
  rw [effectiveNullary_codedProjection_pullback]
  exact numberedSentenceProjection_commutator_norm_le
    (T := T) effectiveExpandedSentenceCode
    effectiveExpandedSentenceCode_surjective
    (effectiveHaltingSentenceLookup e j)
    left right hdistinct mass

end Neoplatonic.LTR.Nullary
