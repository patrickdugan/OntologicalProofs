import Neoplatonic.LTR.NumberedSentenceUltrametric

/-!
Closed balls of radius 2^(-n) are exactly the completions that
agree on the first n numbered sentences.
-/

namespace Neoplatonic.LTR

open FirstOrder

universe u v w
variable {L : FirstOrder.Language.{u,v}} {T : L.Theory} {α : Type w}

theorem numberedSentenceMetric_closedBall_iff_prefix
    (code : ℕ → (L.withConstants α).Sentence)
    (hcode : Function.Surjective code)
    (p q : T.CompleteType α) (n : ℕ) :
    letI : MetricSpace (T.CompleteType α) :=
      numberedSentenceMetric code hcode
    dist q p ≤ (1 / 2 : ℝ)^n ↔
      ∀ i : ℕ, i < n → (code i ∈ q ↔ code i ∈ p) := by
  letI : MetricSpace (T.CompleteType α) :=
    numberedSentenceMetric code hcode
  have hCyl :
      (dist q p ≤ (1 / 2 : ℝ)^n) ↔
      numberedSentenceTruth code q ∈
        PiNat.cylinder (numberedSentenceTruth code p) n := by
    change ((PiNat.dist : Dist (ℕ → Bool)).dist
        (numberedSentenceTruth code q)
        (numberedSentenceTruth code p) ≤ (1 / 2 : ℝ)^n) ↔ _
    exact (PiNat.mem_cylinder_iff_dist_le).symm
  rw [hCyl]
  change (∀ i : ℕ, i < n →
    numberedSentenceTruth code q i = numberedSentenceTruth code p i) ↔
      ∀ i : ℕ, i < n → (code i ∈ q ↔ code i ∈ p)
  constructor
  · intro h i hi
    have heq := h i hi
    constructor
    · intro hq
      have ht : numberedSentenceTruth code q i = true :=
        (numberedSentenceTruth_apply_true_iff code q i).mpr hq
      rw [ht] at heq
      exact (numberedSentenceTruth_apply_true_iff code p i).mp heq.symm
    · intro hp
      have ht : numberedSentenceTruth code p i = true :=
        (numberedSentenceTruth_apply_true_iff code p i).mpr hp
      rw [ht] at heq
      exact (numberedSentenceTruth_apply_true_iff code q i).mp heq
  · intro h i hi
    by_cases hq : code i ∈ q
    · have hp : code i ∈ p := (h i hi).mp hq
      simpa [numberedSentenceTruth, hq, hp]
    · have hp : code i ∉ p := by
        intro hp
        exact hq ((h i hi).mpr hp)
      simpa [numberedSentenceTruth, hq, hp]

end Neoplatonic.LTR
