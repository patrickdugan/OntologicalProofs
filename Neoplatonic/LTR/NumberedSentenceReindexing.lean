import Neoplatonic.LTR.NumberedSentenceFinitePrefix

/-!
# Explicit finite-prefix moduli between logical sentence enumerations

Two surjective sentence numberings induce different first-disagreement
ultrametrics on the same Stone space. An index-lookup map from a target
numbering into a source numbering gives a finite bound on how many
source truth values suffice to recover a prescribed target prefix.

For each target prefix length n, the bound is the maximum of
lookup(j)+1 for j<n. It yields both a finite-prefix transfer theorem
and a direct quantitative continuity modulus between the two metric
presentations. Reversing the enumeration roles gives the inverse
modulus.

The bound is computational relative to the supplied lookup map.
A surjection alone gives such a lookup classically, without a
claim that the lookup is computable.
-/

namespace Neoplatonic.LTR

open FirstOrder

universe u v w
variable {L : FirstOrder.Language.{u,v}} {T : L.Theory} {α : Type w}

/-- The maximum number of source sentence coordinates required to
read the first n coordinates of another enumeration. -/
def sentenceIndexPrefixModulus (lookup : ℕ → ℕ) (n : ℕ) : ℕ :=
  (Finset.range n).sup (fun j => lookup j + 1)

/-- Each target index below n is accessible within the source
prefix prescribed by the index-lookup modulus. -/
theorem sentenceIndexPrefixModulus_gt
    (lookup : ℕ → ℕ) {j n : ℕ} (hj : j < n) :
    lookup j < sentenceIndexPrefixModulus lookup n := by
  have hle : lookup j + 1 ≤
      (Finset.range n).sup (fun i => lookup i + 1) :=
    Finset.le_sup (f := fun i => lookup i + 1) (Finset.mem_range.mpr hj)
  exact (Nat.lt_succ_self _).trans_le hle

/-- An explicitly supplied sentence-index lookup transports
agreement on a sufficiently long prefix of one enumeration to
agreement on the first n sentences of another enumeration. -/
theorem numberedSentencePrefix_transfer_of_lookup
    (source target : ℕ → (L.withConstants α).Sentence)
    (lookup : ℕ → ℕ)
    (hlookup : ∀ j, source (lookup j) = target j)
    (n : ℕ) (p q : T.CompleteType α)
    (hsource : ∀ i, i < sentenceIndexPrefixModulus lookup n →
      (source i ∈ p ↔ source i ∈ q)) :
    ∀ j, j < n → (target j ∈ p ↔ target j ∈ q) := by
  intro j hj
  have hs := hsource (lookup j) (sentenceIndexPrefixModulus_gt lookup hj)
  simpa only [hlookup j] using hs

/-- Surjectivity of the source sentence enumeration supplies a
classical finite-prefix transfer bound for every target prefix. -/
theorem numberedSentencePrefix_transfer
    (source target : ℕ → (L.withConstants α).Sentence)
    (hsource : Function.Surjective source) (n : ℕ) :
    ∃ m, ∀ p q : T.CompleteType α,
      (∀ i, i < m → (source i ∈ p ↔ source i ∈ q)) →
      ∀ j, j < n → (target j ∈ p ↔ target j ∈ q) := by
  classical
  let lookup : ℕ → ℕ := fun j => Classical.choose (hsource (target j))
  have hlookup : ∀ j, source (lookup j) = target j :=
    fun j => Classical.choose_spec (hsource (target j))
  refine ⟨sentenceIndexPrefixModulus lookup n, ?_⟩
  intro p q hp
  exact numberedSentencePrefix_transfer_of_lookup
    source target lookup hlookup n p q hp

/-- The closed ball in a source sentence metric with the explicit
lookup radius maps into the target closed ball of radius 2^(-n). -/
theorem numberedSentenceMetric_radiusTransfer_of_lookup
    (source target : ℕ → (L.withConstants α).Sentence)
    (hsource : Function.Surjective source)
    (htarget : Function.Surjective target)
    (lookup : ℕ → ℕ)
    (hlookup : ∀ j, source (lookup j) = target j)
    (n : ℕ) (p q : T.CompleteType α)
    (hsourceDist : (letI : MetricSpace (T.CompleteType α) :=
      numberedSentenceMetric source hsource; dist q p) ≤ (1 / 2 : ℝ) ^
        sentenceIndexPrefixModulus lookup n) :
    (letI : MetricSpace (T.CompleteType α) :=
      numberedSentenceMetric target htarget; dist q p) ≤ (1 / 2 : ℝ)^n := by
  have hpref : ∀ i, i < sentenceIndexPrefixModulus lookup n →
      (source i ∈ q ↔ source i ∈ p) :=
    (numberedSentenceMetric_closedBall_iff_prefix
      (T := T) source hsource p q (sentenceIndexPrefixModulus lookup n)).mp
        hsourceDist
  have htargetPrefix : ∀ j, j < n → (target j ∈ q ↔ target j ∈ p) :=
    numberedSentencePrefix_transfer_of_lookup
      source target lookup hlookup n q p hpref
  exact (numberedSentenceMetric_closedBall_iff_prefix
    (T := T) target htarget p q n).mpr htargetPrefix

/-- Any two surjective sentence numberings admit a finite
prefix modulus relating their corresponding metric balls. -/
theorem numberedSentenceMetric_radiusTransfer
    (source target : ℕ → (L.withConstants α).Sentence)
    (hsource : Function.Surjective source)
    (htarget : Function.Surjective target)
    (n : ℕ) :
    ∃ m, ∀ p q : T.CompleteType α,
      (letI : MetricSpace (T.CompleteType α) :=
        numberedSentenceMetric source hsource; dist q p) ≤ (1 / 2 : ℝ)^m →
      (letI : MetricSpace (T.CompleteType α) :=
        numberedSentenceMetric target htarget; dist q p) ≤ (1 / 2 : ℝ)^n := by
  classical
  let lookup : ℕ → ℕ := fun j => Classical.choose (hsource (target j))
  have hlookup : ∀ j, source (lookup j) = target j :=
    fun j => Classical.choose_spec (hsource (target j))
  refine ⟨sentenceIndexPrefixModulus lookup n, ?_⟩
  intro p q hd
  exact numberedSentenceMetric_radiusTransfer_of_lookup
    source target hsource htarget lookup hlookup n p q hd

/-- The identity map between any two numbered logical metric
presentations satisfies a quantitative uniform-continuity modulus. -/
theorem numberedSentenceMetric_uniformModulus
    (source target : ℕ → (L.withConstants α).Sentence)
    (hsource : Function.Surjective source)
    (htarget : Function.Surjective target)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p q : T.CompleteType α,
      (letI : MetricSpace (T.CompleteType α) :=
        numberedSentenceMetric source hsource; dist q p) < δ →
      (letI : MetricSpace (T.CompleteType α) :=
        numberedSentenceMetric target htarget; dist q p) < ε := by
  obtain ⟨n, hn⟩ :
      ∃ n : ℕ, (1 / 2 : ℝ)^n < ε :=
    exists_pow_lt_of_lt_one hε (by norm_num)
  obtain ⟨m, hm⟩ :=
    numberedSentenceMetric_radiusTransfer (T := T)
      source target hsource htarget n
  refine ⟨(1 / 2 : ℝ)^m, by positivity, ?_⟩
  intro p q hdist
  exact (hm p q hdist.le).trans_lt hn

end Neoplatonic.LTR
