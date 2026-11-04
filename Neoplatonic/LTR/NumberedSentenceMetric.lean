import Neoplatonic.LTR.LogicalStoneSpectralTriple
import Mathlib.Topology.MetricSpace.PiNat

/-!
# A presentation-sensitive first-disagreement metric on logical Stone spaces

For an explicit surjective sentence enumeration code : ℕ → Sentence,
record each completed theory by the sequence of Boolean truth values
of the numbered sentences. This gives a continuous injective map
from the *actual* Mathlib CompleteType Stone space to Cantor space
ℕ → Bool, equipped with PiNat's first-disagreement metric.

Compactness of the complete-type space and Hausdorffness of Cantor
space make the truth-sequence map an embedding. Pulling back the
PiNat metric along that embedding gives a metric that induces the
existing Stone topology, with exact first-disagreement distance

  dist(p,q) = 0 if p=q
            = (1/2)^(firstDiff (truth p) (truth q)) otherwise.

The code is an explicit assumption and may be a noncomputable
enumeration; computing truth values of completed theories does
not follow from computability of the sentence numbering.
-/

namespace Neoplatonic.LTR

open FirstOrder Set TopologicalSpace Topology
open FirstOrder.Language.Theory

universe u v w

variable {L : FirstOrder.Language.{u,v}} {T : L.Theory} {α : Type w}

/-- Boolean truth sequence of a complete first-order type, in the
order given by a sentence numbering. -/
noncomputable def numberedSentenceTruth
    (code : ℕ → (L.withConstants α).Sentence)
    (p : T.CompleteType α) : ℕ → Bool :=
  fun n => by
    classical
    exact decide (code n ∈ p)

/-- A numbered Boolean coordinate reads membership of the sentence. -/
theorem numberedSentenceTruth_apply_true_iff
    (code : ℕ → (L.withConstants α).Sentence)
    (p : T.CompleteType α) (n : ℕ) :
    numberedSentenceTruth code p n = true ↔ code n ∈ p := by
  classical
  simp [numberedSentenceTruth]

/-- Each truth coordinate is continuous because the truth locus of
the corresponding sentence is clopen in the Stone topology. -/
theorem numberedSentenceTruth_continuous
    (code : ℕ → (L.withConstants α).Sentence) :
    Continuous (numberedSentenceTruth (T := T) code) := by
  apply continuous_pi_iff.mpr
  intro n
  have hc : IsClopen (T.typesWith (code n)) :=
    locus_isClopen (T := T) (α := α) (code n)
  have ht : {p : T.CompleteType α |
      numberedSentenceTruth code p n = true} = T.typesWith (code n) := by
    ext p
    simp [numberedSentenceTruth]
  have hf : {p : T.CompleteType α |
      numberedSentenceTruth code p n = false} =
        (T.typesWith (code n))ᶜ := by
    ext p
    simp [numberedSentenceTruth]
  have hb (b : Bool) :
      IsOpen {p : T.CompleteType α |
        numberedSentenceTruth code p n = b} := by
    cases b with
    | false =>
      rw [hf]
      exact hc.1.isOpen_compl
    | true =>
      rw [ht]
      exact hc.2
  apply continuous_def.mpr
  intro s hs
  have heq :
      (fun p : T.CompleteType α => numberedSentenceTruth code p n) ⁻¹' s =
      ⋃ b : s, {p : T.CompleteType α |
        numberedSentenceTruth code p n = b.val} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro hp
      exact ⟨⟨numberedSentenceTruth code p n, hp⟩, rfl⟩
    · rintro ⟨b, hb'⟩
      rw [hb']
      exact b.property
  rw [heq]
  exact isOpen_iUnion (fun b => hb b.val)

/-- A surjective sentence numbering separates distinct completed
theories, making the Boolean truth-stream encoding injective. -/
theorem numberedSentenceTruth_injective
    (code : ℕ → (L.withConstants α).Sentence)
    (hcode : Function.Surjective code) :
    Function.Injective (numberedSentenceTruth (T := T) code) := by
  intro p q h
  apply SetLike.ext
  intro φ
  obtain ⟨n, hn⟩ := hcode φ
  have hcoord : numberedSentenceTruth code p n =
      numberedSentenceTruth code q n :=
    congrArg (fun bits : ℕ → Bool => bits n) h
  have hiff : code n ∈ p ↔ code n ∈ q := by
    constructor
    · intro hp
      have ht : numberedSentenceTruth code p n = true :=
        (numberedSentenceTruth_apply_true_iff code p n).mpr hp
      rw [ht] at hcoord
      exact (numberedSentenceTruth_apply_true_iff code q n).mp hcoord.symm
    · intro hq
      have ht : numberedSentenceTruth code q n = true :=
        (numberedSentenceTruth_apply_true_iff code q n).mpr hq
      rw [ht] at hcoord
      exact (numberedSentenceTruth_apply_true_iff code p n).mp hcoord
  simpa [hn] using hiff

/-- The countable Boolean truth sequence is a genuine Stone-space
embedding into Cantor space, by compact-to-Hausdorff embedding. -/
theorem numberedSentenceTruth_isEmbedding
    (code : ℕ → (L.withConstants α).Sentence)
    (hcode : Function.Surjective code) :
    IsEmbedding (numberedSentenceTruth (T := T) code) := by
  letI : MetricSpace (ℕ → Bool) := (PiNat.metricSpace : MetricSpace (ℕ → Bool))
  exact ((numberedSentenceTruth_continuous (T := T) code).isClosedEmbedding
    (numberedSentenceTruth_injective (T := T) code hcode)).isEmbedding

/-- The metric induced by the explicit sentence truth numbering is
compatible with Mathlib's original complete-type Stone topology. -/
noncomputable abbrev numberedSentenceMetric
    (code : ℕ → (L.withConstants α).Sentence)
    (hcode : Function.Surjective code) :
    MetricSpace (T.CompleteType α) := by
  letI : MetricSpace (ℕ → Bool) := (PiNat.metricSpace : MetricSpace (ℕ → Bool))
  exact (numberedSentenceTruth_isEmbedding (T := T) code hcode).comapMetricSpace
    (numberedSentenceTruth code)

/-- The induced distance is exactly PiNat's first-disagreement
distance between the truth sequences. -/
theorem numberedSentenceMetric_dist
    (code : ℕ → (L.withConstants α).Sentence)
    (hcode : Function.Surjective code)
    (p q : T.CompleteType α) :
    letI : MetricSpace (T.CompleteType α) :=
      numberedSentenceMetric code hcode
    dist p q = (PiNat.dist : Dist (ℕ → Bool)).dist
      (numberedSentenceTruth code p) (numberedSentenceTruth code q) := by
  letI : MetricSpace (ℕ → Bool) := (PiNat.metricSpace : MetricSpace (ℕ → Bool))
  letI : MetricSpace (T.CompleteType α) :=
    numberedSentenceMetric code hcode
  rfl

/-- A pair of distinct completions lies at distance 2^(-n),
where n is the first numbered sentence they disagree about. -/
theorem numberedSentenceMetric_firstDisagreement
    (code : ℕ → (L.withConstants α).Sentence)
    (hcode : Function.Surjective code)
    (p q : T.CompleteType α) (hpq : p ≠ q) :
    letI : MetricSpace (T.CompleteType α) :=
      numberedSentenceMetric code hcode
    dist p q = (1 / 2 : ℝ) ^
      PiNat.firstDiff (numberedSentenceTruth code p)
        (numberedSentenceTruth code q) := by
  letI : MetricSpace (ℕ → Bool) := (PiNat.metricSpace : MetricSpace (ℕ → Bool))
  letI : MetricSpace (T.CompleteType α) :=
    numberedSentenceMetric code hcode
  have hne : numberedSentenceTruth code p ≠
      numberedSentenceTruth code q := by
    intro h
    exact hpq (numberedSentenceTruth_injective (T := T) code hcode h)
  rw [numberedSentenceMetric_dist code hcode p q]
  exact PiNat.dist_eq_of_ne hne

/-- Every named logical truth locus is open under the numbered
sentence metric, because it induces the original Stone topology. -/
theorem numberedSentenceMetric_locus_isOpen
    (code : ℕ → (L.withConstants α).Sentence)
    (hcode : Function.Surjective code)
    (φ : (L.withConstants α).Sentence) :
    letI : MetricSpace (T.CompleteType α) :=
      numberedSentenceMetric code hcode
    IsOpen (T.typesWith φ) := by
  letI : MetricSpace (T.CompleteType α) :=
    numberedSentenceMetric code hcode
  exact (locus_isClopen (T := T) (α := α) φ).isOpen

end Neoplatonic.LTR
