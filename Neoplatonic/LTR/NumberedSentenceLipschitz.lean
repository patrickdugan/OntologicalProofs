import Neoplatonic.LTR.NumberedStoneSpectralTriple
import Neoplatonic.LTR.ComplexLogicalSpectral

/-!
# Quantitative gradients of numbered sentence truth projections

The nth coordinate of PiNat's first-disagreement metric cannot
change when the metric distance is below 2^(-n). Therefore the
complex characteristic function of the nth enumerated sentence
has Lipschitz constant at most 2^n.

This supplies an explicit numerical operator-commutator bound for
the numbered sentence, uniformly over every nondegenerate
marked-edge sequence and every real diagonal Dirac mass sequence.

It is an index-relative estimate. Although code can be computable,
the Boolean truth sequence of a general completion is not assumed
computable.
-/

namespace Neoplatonic.LTR

open FirstOrder Set TopologicalSpace
open FirstOrder.Language.Theory

universe u v w

variable {L : FirstOrder.Language.{u,v}} {T : L.Theory} {α : Type w}

/-- Agreement of numbered truth values at index n follows
from distance strictly below 2^(-n). -/
theorem numberedSentenceMetric_agree_at_of_dist_lt
    (code : ℕ → (L.withConstants α).Sentence)
    (hcode : Function.Surjective code)
    (p q : T.CompleteType α) (n : ℕ)
    (hd : (letI : MetricSpace (T.CompleteType α) :=
      numberedSentenceMetric code hcode
      dist p q) < (1 / 2 : ℝ)^n) :
    code n ∈ p ↔ code n ∈ q := by
  letI : MetricSpace (ℕ → Bool) :=
    (PiNat.metricSpace : MetricSpace (ℕ → Bool))
  letI : MetricSpace (T.CompleteType α) :=
    numberedSentenceMetric code hcode
  have hdBits :
      (PiNat.dist : Dist (ℕ → Bool)).dist
          (numberedSentenceTruth code p)
          (numberedSentenceTruth code q) < (1 / 2 : ℝ)^n := by
    rwa [numberedSentenceMetric_dist code hcode p q] at hd
  have heq : numberedSentenceTruth code p n =
      numberedSentenceTruth code q n :=
    PiNat.apply_eq_of_dist_lt hdBits (le_refl n)
  constructor
  · intro hp
    have ht : numberedSentenceTruth code p n = true :=
      (numberedSentenceTruth_apply_true_iff code p n).mpr hp
    rw [ht] at heq
    exact (numberedSentenceTruth_apply_true_iff code q n).mp heq.symm
  · intro hq
    have ht : numberedSentenceTruth code q n = true :=
      (numberedSentenceTruth_apply_true_iff code q n).mpr hq
    rw [ht] at heq
    exact (numberedSentenceTruth_apply_true_iff code p n).mp heq

/-- If two completions disagree on the nth numbered sentence,
their numbered Stone distance is at least 2^(-n). -/
theorem numberedSentenceMetric_dist_lower_of_disagreement
    (code : ℕ → (L.withConstants α).Sentence)
    (hcode : Function.Surjective code)
    (p q : T.CompleteType α) (n : ℕ)
    (hne : ¬ (code n ∈ p ↔ code n ∈ q)) :
    letI : MetricSpace (T.CompleteType α) :=
      numberedSentenceMetric code hcode
    (1 / 2 : ℝ)^n ≤ dist p q := by
  letI : MetricSpace (T.CompleteType α) :=
    numberedSentenceMetric code hcode
  by_contra h
  have hlt : dist p q < (1 / 2 : ℝ)^n := lt_of_not_ge h
  exact hne (numberedSentenceMetric_agree_at_of_dist_lt
    code hcode p q n hlt)

/-- The continuous complex truth projection for code(n) is
globally 2^n-Lipschitz for the sentence-numbered metric. -/
theorem numberedSentenceProjection_lipschitz
    (code : ℕ → (L.withConstants α).Sentence)
    (hcode : Function.Surjective code)
    (n : ℕ) :
    letI : MetricSpace (T.CompleteType α) :=
      numberedSentenceMetric code hcode
    ∀ p q : T.CompleteType α,
      ‖complexLogicalProjection (T := T) (code n) p -
        complexLogicalProjection (T := T) (code n) q‖ ≤
        (2 : ℝ)^n * dist p q := by
  letI : MetricSpace (T.CompleteType α) :=
    numberedSentenceMetric code hcode
  intro p q
  have hnonneg : 0 ≤ (2 : ℝ)^n * dist p q := by positivity
  have hcross (hdis : ¬ (code n ∈ p ↔ code n ∈ q)) :
      (1 : ℝ) ≤ (2 : ℝ)^n * dist p q := by
    have hgap :=
      numberedSentenceMetric_dist_lower_of_disagreement
        code hcode p q n hdis
    calc
      (1 : ℝ) = (2 : ℝ)^n * (1 / 2 : ℝ)^n := by
        rw [← mul_pow]
        norm_num
      _ ≤ (2 : ℝ)^n * dist p q :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
  by_cases hp : code n ∈ p
  · by_cases hq : code n ∈ q
    · rw [complexLogicalProjection_apply_mem (T := T) (code n) p hp,
        complexLogicalProjection_apply_mem (T := T) (code n) q hq]
      simpa using hnonneg
    · rw [complexLogicalProjection_apply_mem (T := T) (code n) p hp,
        complexLogicalProjection_apply_not_mem (T := T) (code n) q hq]
      simpa using hcross (by simp [hp, hq])
  · by_cases hq : code n ∈ q
    · rw [complexLogicalProjection_apply_not_mem (T := T) (code n) p hp,
        complexLogicalProjection_apply_mem (T := T) (code n) q hq]
      simpa using hcross (by simp [hp, hq])
    · rw [complexLogicalProjection_apply_not_mem (T := T) (code n) p hp,
        complexLogicalProjection_apply_not_mem (T := T) (code n) q hq]
      simpa using hnonneg

/-- The nth sentence projection is in the finite-Lipschitz
star subalgebra, with the explicit witness 2^n. -/
theorem numberedSentenceProjection_mem_Lipschitz
    (code : ℕ → (L.withConstants α).Sentence)
    (hcode : Function.Surjective code)
    (n : ℕ) :
    letI : MetricSpace (T.CompleteType α) :=
      numberedSentenceMetric code hcode
    complexLogicalProjection (T := T) (code n) ∈
      compactComplexLipschitzStarSubalgebra (T.CompleteType α) := by
  letI : MetricSpace (T.CompleteType α) :=
    numberedSentenceMetric code hcode
  change HasFiniteComplexLipschitzConstant
    (complexLogicalProjection (T := T) (code n))
  exact ⟨(2 : ℝ)^n, by positivity,
    numberedSentenceProjection_lipschitz code hcode n⟩

/-- An explicit 2^n uniform upper bound on the *actual infinite
complex Hilbert commutator* for the nth numbered sentence projection,
for arbitrary nondegenerate marked edges and any Dirac masses. -/
theorem numberedSentenceProjection_commutator_norm_le
    (code : ℕ → (L.withConstants α).Sentence)
    (hcode : Function.Surjective code)
    (n : ℕ)
    (left right : ℕ → T.CompleteType α)
    (hdistinct : ∀ j, left j ≠ right j)
    (mass : ℕ → ℝ) :
    letI : MetricSpace (T.CompleteType α) :=
      numberedSentenceMetric code hcode
    ∃ (hEdge : ∀ j,
      |(dist (left j) (right j))⁻¹| *
        ‖complexLogicalProjection (T := T) (code n) (right j) -
          complexLogicalProjection (T := T) (code n) (left j)‖ ≤
          (2 : ℝ)^n),
      ‖complexValuedPairCommutatorCLM
          mass
          (fun j => (dist (left j) (right j))⁻¹)
          (fun j => complexLogicalProjection (T := T) (code n) (left j))
          (fun j => complexLogicalProjection (T := T) (code n) (right j))
          ((2 : ℝ)^n) (by positivity) hEdge‖ ≤
        (2 : ℝ)^n := by
  letI : MetricSpace (T.CompleteType α) :=
    numberedSentenceMetric code hcode
  have hlip := numberedSentenceProjection_lipschitz code hcode n
  have hEdge : ∀ j,
      |(dist (left j) (right j))⁻¹| *
        ‖complexLogicalProjection (T := T) (code n) (right j) -
          complexLogicalProjection (T := T) (code n) (left j)‖ ≤
          (2 : ℝ)^n := by
    intro j
    exact (complexMarkedEdgeBound_iff
      (left j) (right j) (hdistinct j)
      (complexLogicalProjection (T := T) (code n))
      ((2 : ℝ)^n)).mpr (hlip (left j) (right j))
  refine ⟨hEdge, ?_⟩
  exact complexValuedPairCommutatorCLM_norm_le
    mass
    (fun j => (dist (left j) (right j))⁻¹)
    (fun j => complexLogicalProjection (T := T) (code n) (left j))
    (fun j => complexLogicalProjection (T := T) (code n) (right j))
    ((2 : ℝ)^n) (by positivity) hEdge

end Neoplatonic.LTR
