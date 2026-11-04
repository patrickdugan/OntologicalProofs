import Neoplatonic.LTR.NumberedSemanticMapModulus

/-!
# Composition laws for indexed logical interpretations

Suppose F maps complete types from theory T₁ to T₂, and G maps
complete types from T₂ to T₃. If each map satisfies the usual
sentence-truth pullback law via index lookups k and l, then
G ∘ F satisfies the same law via k ∘ l.

The required finite source-prefix bound for a target prefix of
length n is at most the nested modulus M_k(M_l(n)). This
provides a compositional quantitative metric bound under the
first-disagreement ultrametrics.

These are conditional interpretation laws; they assume the
sentence-level truth equations rather than inventing them.
-/

namespace Neoplatonic.LTR

open FirstOrder

universe u₁ v₁ w₁ u₂ v₂ w₂ u₃ v₃ w₃
variable {L₁ : FirstOrder.Language.{u₁,v₁}}
variable {L₂ : FirstOrder.Language.{u₂,v₂}}
variable {L₃ : FirstOrder.Language.{u₃,v₃}}
variable {T₁ : L₁.Theory} {T₂ : L₂.Theory} {T₃ : L₃.Theory}
variable {α₁ : Type w₁} {α₂ : Type w₂} {α₃ : Type w₃}

/-- The prefix modulus of a composite lookup is bounded by
the successive moduli of the two component lookups. -/
theorem sentenceIndexPrefixModulus_comp_le
    (first second : ℕ → ℕ) (n : ℕ) :
    sentenceIndexPrefixModulus (first ∘ second) n ≤
      sentenceIndexPrefixModulus first
        (sentenceIndexPrefixModulus second n) := by
  unfold sentenceIndexPrefixModulus
  apply Finset.sup_le
  intro j hj
  have hlt : second j < sentenceIndexPrefixModulus second n :=
    sentenceIndexPrefixModulus_gt second (Finset.mem_range.mp hj)
  exact Finset.le_sup (f := fun i => first i + 1)
    (Finset.mem_range.mpr hlt)

/-- Syntactic index translations compose contravariantly with
the maps they induce on complete-type Stone spaces. -/
theorem numberedSemanticMap_comp_truth
    (source : ℕ → (L₁.withConstants α₁).Sentence)
    (middle : ℕ → (L₂.withConstants α₂).Sentence)
    (target : ℕ → (L₃.withConstants α₃).Sentence)
    (F : T₁.CompleteType α₁ → T₂.CompleteType α₂)
    (G : T₂.CompleteType α₂ → T₃.CompleteType α₃)
    (k l : ℕ → ℕ)
    (hF : ∀ j (p : T₁.CompleteType α₁),
      middle j ∈ F p ↔ source (k j) ∈ p)
    (hG : ∀ j (q : T₂.CompleteType α₂),
      target j ∈ G q ↔ middle (l j) ∈ q) :
    ∀ j (p : T₁.CompleteType α₁),
      target j ∈ (G ∘ F) p ↔ source ((k ∘ l) j) ∈ p := by
  intro j p
  exact (hG j (F p)).trans (hF (l j) p)

/-- Finite logical observation bounds compose: knowledge of the
source prefix of length M_k(M_l(n)) determines the n target
truth values after applying G ∘ F. -/
theorem numberedSemanticMap_comp_prefixTransfer
    (source : ℕ → (L₁.withConstants α₁).Sentence)
    (middle : ℕ → (L₂.withConstants α₂).Sentence)
    (target : ℕ → (L₃.withConstants α₃).Sentence)
    (F : T₁.CompleteType α₁ → T₂.CompleteType α₂)
    (G : T₂.CompleteType α₂ → T₃.CompleteType α₃)
    (k l : ℕ → ℕ)
    (hF : ∀ j (p : T₁.CompleteType α₁),
      middle j ∈ F p ↔ source (k j) ∈ p)
    (hG : ∀ j (q : T₂.CompleteType α₂),
      target j ∈ G q ↔ middle (l j) ∈ q)
    (n : ℕ) (p q : T₁.CompleteType α₁)
    (hsource : ∀ i,
      i < sentenceIndexPrefixModulus k
        (sentenceIndexPrefixModulus l n) →
        (source i ∈ p ↔ source i ∈ q)) :
    ∀ j, j < n →
      (target j ∈ (G ∘ F) p ↔ target j ∈ (G ∘ F) q) := by
  have hmiddle : ∀ i, i < sentenceIndexPrefixModulus l n →
      (middle i ∈ F p ↔ middle i ∈ F q) :=
    numberedSemanticMap_prefixTransfer
      source middle F k hF (sentenceIndexPrefixModulus l n) p q hsource
  exact numberedSemanticMap_prefixTransfer
    middle target G l hG n (F p) (F q) hmiddle

/-- The metric bound of a composite truth-preserving map is
controlled by the nested finite-prefix modulus. -/
theorem numberedSemanticMap_comp_radiusTransfer
    (source : ℕ → (L₁.withConstants α₁).Sentence)
    (middle : ℕ → (L₂.withConstants α₂).Sentence)
    (target : ℕ → (L₃.withConstants α₃).Sentence)
    (hsrc : Function.Surjective source)
    (hmid : Function.Surjective middle)
    (htar : Function.Surjective target)
    (F : T₁.CompleteType α₁ → T₂.CompleteType α₂)
    (G : T₂.CompleteType α₂ → T₃.CompleteType α₃)
    (k l : ℕ → ℕ)
    (hF : ∀ j (p : T₁.CompleteType α₁),
      middle j ∈ F p ↔ source (k j) ∈ p)
    (hG : ∀ j (q : T₂.CompleteType α₂),
      target j ∈ G q ↔ middle (l j) ∈ q)
    (n : ℕ) (p q : T₁.CompleteType α₁)
    (hnear :
      (letI : MetricSpace (T₁.CompleteType α₁) :=
        numberedSentenceMetric source hsrc; dist q p) ≤
        (1 / 2 : ℝ)^sentenceIndexPrefixModulus k
          (sentenceIndexPrefixModulus l n)) :
    (letI : MetricSpace (T₃.CompleteType α₃) :=
      numberedSentenceMetric target htar; dist (G (F q)) (G (F p))) ≤
        (1 / 2 : ℝ)^n := by
  have hmiddle :
      (letI : MetricSpace (T₂.CompleteType α₂) :=
        numberedSentenceMetric middle hmid; dist (F q) (F p)) ≤
        (1 / 2 : ℝ)^sentenceIndexPrefixModulus l n :=
    numberedSemanticMap_radiusTransfer
      source middle hsrc hmid F k hF
      (sentenceIndexPrefixModulus l n) p q hnear
  exact numberedSemanticMap_radiusTransfer
    middle target hmid htar G l hG n (F p) (F q) hmiddle

end Neoplatonic.LTR
