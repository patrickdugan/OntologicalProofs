import Neoplatonic.LTR.NumberedSentenceLipschitz

/-! The numbered first-disagreement Stone metric is non-Archimedean. -/

namespace Neoplatonic.LTR

open FirstOrder

universe u v w
variable {L : FirstOrder.Language.{u,v}} {T : L.Theory} {α : Type w}

theorem numberedSentenceMetric_ultrametric
    (code : ℕ → (L.withConstants α).Sentence)
    (hcode : Function.Surjective code)
    (p q r : T.CompleteType α) :
    letI : MetricSpace (T.CompleteType α) :=
      numberedSentenceMetric code hcode
    dist p r ≤ max (dist p q) (dist q r) := by
  letI : MetricSpace (T.CompleteType α) :=
    numberedSentenceMetric code hcode
  change (PiNat.dist : Dist (ℕ → Bool)).dist
      (numberedSentenceTruth code p)
      (numberedSentenceTruth code r) ≤
    max ((PiNat.dist : Dist (ℕ → Bool)).dist
      (numberedSentenceTruth code p) (numberedSentenceTruth code q))
      ((PiNat.dist : Dist (ℕ → Bool)).dist
        (numberedSentenceTruth code q) (numberedSentenceTruth code r))
  exact PiNat.dist_triangle_nonarch
    (numberedSentenceTruth code p)
    (numberedSentenceTruth code q)
    (numberedSentenceTruth code r)

end Neoplatonic.LTR
