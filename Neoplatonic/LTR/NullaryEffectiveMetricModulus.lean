import Neoplatonic.LTR.NullaryEffectiveSyntax

/-!
# Executable prefix moduli for genuine nullary first-order maps

The full expanded-sentence numbering and index lookup are defined
constructively through Mathlib's verified formula encoding and
decoding, rather than by selecting preimages using Classical.choose.

The modulus below is a finite maximum over a total natural-number
function. Every constituent has an explicit Lean definition.
Its exact semantic and metric correctness is inherited from the
verified full-sentence truth-pullback law and numbered Stone metric.

This establishes a computable *definition* of the modulus in Lean.
It does not yet prove an instance of Mathlib's stronger
Primrec / Computable function predicate for the syntax substitution.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language

/-- The finite index budget for the first n output sentences of
the genuine syntactic map of the partial-recursive code e. -/
def effectiveSentencePrefixModulus (e : Nat.Partrec.Code)
    (n : ℕ) : ℕ :=
  sentenceIndexPrefixModulus (effectiveHaltingSentenceLookup e) n

/-- The direct finite-index modulus dominates every translated
sentence index in the required initial prefix. -/
theorem effectiveSentencePrefixModulus_gt
    (e : Nat.Partrec.Code) (n j : ℕ)
    (hj : j < n) :
    effectiveHaltingSentenceLookup e j <
      effectiveSentencePrefixModulus e n :=
  sentenceIndexPrefixModulus_gt
    (effectiveHaltingSentenceLookup e) hj

/-- Sufficient source truth-prefix agreement forces output
truth-prefix agreement for every expanded first-order sentence. -/
theorem effectiveSyntaxMap_prefixTransfer
    (e : Nat.Partrec.Code)
    (n : ℕ) (p q : T.CompleteType Empty)
    (hsource : ∀ i, i < effectiveSentencePrefixModulus e n →
      (effectiveExpandedSentenceCode i ∈ p ↔
       effectiveExpandedSentenceCode i ∈ q)) :
    ∀ j, j < n →
      (effectiveExpandedSentenceCode j ∈ syntaxMap e p ↔
       effectiveExpandedSentenceCode j ∈ syntaxMap e q) := by
  exact numberedSemanticMap_prefixTransfer
    effectiveExpandedSentenceCode effectiveExpandedSentenceCode
    (syntaxMap e) (effectiveHaltingSentenceLookup e)
    (effectiveHaltingSentenceLookup_truth e)
    n p q hsource

/-- The full-sentence first-disagreement Stone metric transfers
at the explicitly computed finite prefix budget. -/
theorem effectiveSyntaxMap_radiusTransfer
    (e : Nat.Partrec.Code)
    (n : ℕ) (p q : T.CompleteType Empty)
    (hnear :
      (letI : MetricSpace (T.CompleteType Empty) :=
        numberedSentenceMetric effectiveExpandedSentenceCode
          effectiveExpandedSentenceCode_surjective;
        dist q p) ≤
          (1 / 2 : ℝ)^effectiveSentencePrefixModulus e n) :
    (letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric effectiveExpandedSentenceCode
        effectiveExpandedSentenceCode_surjective;
      dist (syntaxMap e q) (syntaxMap e p)) ≤
        (1 / 2 : ℝ)^n := by
  exact numberedSemanticMap_radiusTransfer
    effectiveExpandedSentenceCode effectiveExpandedSentenceCode
    effectiveExpandedSentenceCode_surjective
    effectiveExpandedSentenceCode_surjective
    (syntaxMap e) (effectiveHaltingSentenceLookup e)
    (effectiveHaltingSentenceLookup_truth e)
    n p q hnear

/-- Uniform continuity with an explicit finite natural-number
modulus, for the executable sentence numbering. -/
theorem effectiveSyntaxMap_uniformModulus
    (e : Nat.Partrec.Code)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ,
      (1 / 2 : ℝ)^n < ε ∧
      ∀ p q : T.CompleteType Empty,
        (letI : MetricSpace (T.CompleteType Empty) :=
          numberedSentenceMetric effectiveExpandedSentenceCode
            effectiveExpandedSentenceCode_surjective;
          dist q p) ≤
            (1 / 2 : ℝ)^effectiveSentencePrefixModulus e n →
        (letI : MetricSpace (T.CompleteType Empty) :=
          numberedSentenceMetric effectiveExpandedSentenceCode
            effectiveExpandedSentenceCode_surjective;
          dist (syntaxMap e q) (syntaxMap e p)) < ε := by
  obtain ⟨n, hn⟩ :
      ∃ n : ℕ, (1 / 2 : ℝ)^n < ε :=
    exists_pow_lt_of_lt_one hε (by norm_num)
  refine ⟨n, hn, ?_⟩
  intro p q hp
  exact (effectiveSyntaxMap_radiusTransfer e n p q hp).trans_lt hn

/-- Composing two direct syntax lookups has its natural finite
prefix modulus bounded by the nested computed moduli. -/
theorem effectiveSentencePrefixModulus_comp_le
    (e f : Nat.Partrec.Code) (n : ℕ) :
    sentenceIndexPrefixModulus
      (effectiveHaltingSentenceLookup e ∘
        effectiveHaltingSentenceLookup f) n ≤
      effectiveSentencePrefixModulus e
        (effectiveSentencePrefixModulus f n) :=
  sentenceIndexPrefixModulus_comp_le
    (effectiveHaltingSentenceLookup e)
    (effectiveHaltingSentenceLookup f) n

/-- The corresponding exact metric implication for two actual
program-induced complete-theory maps, with the direct lookup
moduli rather than classical preimage choices. -/
theorem effectiveSyntaxMap_comp_radiusTransfer
    (e f : Nat.Partrec.Code)
    (n : ℕ) (p q : T.CompleteType Empty)
    (hnear :
      (letI : MetricSpace (T.CompleteType Empty) :=
        numberedSentenceMetric effectiveExpandedSentenceCode
          effectiveExpandedSentenceCode_surjective;
        dist q p) ≤
          (1 / 2 : ℝ)^effectiveSentencePrefixModulus e
            (effectiveSentencePrefixModulus f n)) :
    (letI : MetricSpace (T.CompleteType Empty) :=
      numberedSentenceMetric effectiveExpandedSentenceCode
        effectiveExpandedSentenceCode_surjective;
      dist (syntaxMap f (syntaxMap e q))
        (syntaxMap f (syntaxMap e p))) ≤ (1 / 2 : ℝ)^n := by
  exact numberedSemanticMap_comp_radiusTransfer
    effectiveExpandedSentenceCode effectiveExpandedSentenceCode
    effectiveExpandedSentenceCode
    effectiveExpandedSentenceCode_surjective
    effectiveExpandedSentenceCode_surjective
    effectiveExpandedSentenceCode_surjective
    (syntaxMap e) (syntaxMap f)
    (effectiveHaltingSentenceLookup e)
    (effectiveHaltingSentenceLookup f)
    (effectiveHaltingSentenceLookup_truth e)
    (effectiveHaltingSentenceLookup_truth f)
    n p q hnear

end Neoplatonic.LTR.Nullary
