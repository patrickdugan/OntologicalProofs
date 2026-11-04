import Neoplatonic.LTR.NumberedSentenceReindexing

/-!
# Quantitative continuity of sentence-preserving logical maps

A map between first-order Stone spaces that preserves every numbered
target sentence via an explicit source-index lookup has a finite
prefix modulus. On the corresponding first-disagreement ultrametrics,
the same lookup supplies a concrete metric continuity modulus.

This is the elementary geometric side of syntax/Stone contravariance:
an interpretation that translates each target sentence to a source
sentence induces continuity of its completion-space map.

The theorem requires the complete-type truth equivalence as a
hypothesis. For the explicit nullary language, that equivalence was
proved previously on lifted original-language sentences. Establishing
it for a chosen surjective enumeration of every expanded sentence is
an additional presentation step.

The theorem concerns the mapped points and metric bounds. It does
not postulate a unitary Dirac intertwiner or any computability oracle.
-/

namespace Neoplatonic.LTR

open FirstOrder

universe u₁ v₁ w₁ u₂ v₂ w₂
variable {L₁ : FirstOrder.Language.{u₁,v₁}}
variable {L₂ : FirstOrder.Language.{u₂,v₂}}
variable {T₁ : L₁.Theory} {T₂ : L₂.Theory}
variable {α₁ : Type w₁} {α₂ : Type w₂}

/-- A semantic map with an index translation preserves finite
truth prefixes with the explicit lookup modulus. -/
theorem numberedSemanticMap_prefixTransfer
    (source : ℕ → (L₁.withConstants α₁).Sentence)
    (target : ℕ → (L₂.withConstants α₂).Sentence)
    (F : T₁.CompleteType α₁ → T₂.CompleteType α₂)
    (lookup : ℕ → ℕ)
    (htruth : ∀ j (p : T₁.CompleteType α₁),
      target j ∈ F p ↔ source (lookup j) ∈ p)
    (n : ℕ) (p q : T₁.CompleteType α₁)
    (hsource : ∀ i, i < sentenceIndexPrefixModulus lookup n →
      (source i ∈ p ↔ source i ∈ q)) :
    ∀ j, j < n → (target j ∈ F p ↔ target j ∈ F q) := by
  intro j hj
  have hsrc := hsource (lookup j)
    (sentenceIndexPrefixModulus_gt lookup hj)
  exact (htruth j p).trans (hsrc.trans (htruth j q).symm)

/-- The source sentence ball at the lookup modulus maps into
the target sentence ball of the requested radius. -/
theorem numberedSemanticMap_radiusTransfer
    (source : ℕ → (L₁.withConstants α₁).Sentence)
    (target : ℕ → (L₂.withConstants α₂).Sentence)
    (hsurj : Function.Surjective source)
    (htsurj : Function.Surjective target)
    (F : T₁.CompleteType α₁ → T₂.CompleteType α₂)
    (lookup : ℕ → ℕ)
    (htruth : ∀ j (p : T₁.CompleteType α₁),
      target j ∈ F p ↔ source (lookup j) ∈ p)
    (n : ℕ) (p q : T₁.CompleteType α₁)
    (hnear :
      (letI : MetricSpace (T₁.CompleteType α₁) :=
        numberedSentenceMetric source hsurj; dist q p) ≤
          (1 / 2 : ℝ)^sentenceIndexPrefixModulus lookup n) :
    (letI : MetricSpace (T₂.CompleteType α₂) :=
      numberedSentenceMetric target htsurj; dist (F q) (F p)) ≤
        (1 / 2 : ℝ)^n := by
  have hsourcePref : ∀ i, i < sentenceIndexPrefixModulus lookup n →
      (source i ∈ q ↔ source i ∈ p) :=
    (numberedSentenceMetric_closedBall_iff_prefix
      (T := T₁) source hsurj p q
        (sentenceIndexPrefixModulus lookup n)).mp hnear
  have htargetPref : ∀ j, j < n →
      (target j ∈ F q ↔ target j ∈ F p) :=
    numberedSemanticMap_prefixTransfer
      source target F lookup htruth n q p hsourcePref
  exact (numberedSentenceMetric_closedBall_iff_prefix
    (T := T₂) target htsurj (F p) (F q) n).mpr htargetPref

/-- An explicit index-translation lookup gives a quantitative
uniform-continuity modulus for the map of logical Stone completions. -/
theorem numberedSemanticMap_uniformModulus
    (source : ℕ → (L₁.withConstants α₁).Sentence)
    (target : ℕ → (L₂.withConstants α₂).Sentence)
    (hsurj : Function.Surjective source)
    (htsurj : Function.Surjective target)
    (F : T₁.CompleteType α₁ → T₂.CompleteType α₂)
    (lookup : ℕ → ℕ)
    (htruth : ∀ j (p : T₁.CompleteType α₁),
      target j ∈ F p ↔ source (lookup j) ∈ p)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p q : T₁.CompleteType α₁,
      (letI : MetricSpace (T₁.CompleteType α₁) :=
        numberedSentenceMetric source hsurj; dist q p) < δ →
      (letI : MetricSpace (T₂.CompleteType α₂) :=
        numberedSentenceMetric target htsurj; dist (F q) (F p)) < ε := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ)^n < ε :=
    exists_pow_lt_of_lt_one hε (by norm_num)
  refine ⟨(1 / 2 : ℝ)^sentenceIndexPrefixModulus lookup n,
    by positivity, ?_⟩
  intro p q hnear
  exact (numberedSemanticMap_radiusTransfer
    source target hsurj htsurj F lookup htruth n p q hnear.le).trans_lt hn

end Neoplatonic.LTR
