import Neoplatonic.LTR.ManifestationCapacity

/-!
# Pointwise recovery versus uniform finite-sample obstruction

An arbitrary dense sequence of genuine complete first-order theories
eventually detects each *fixed* nonempty sentence truth locus. The
two-valued finite detection norm therefore eventually equals the
norm of its continuous complex truth projection.

At every fixed finite depth, one explicit diagonal sentence has a
norm-one projection and is refuted by all sampled theories. So the
maximum possible discrepancy is attained afresh at every depth.

These statements concern logical truth projections, not spectral
truncation errors for arbitrary operators or physical embodiment.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder

/-- The finite-sample 0/1 norm of a sentence truth observable.
The empty sample (N=0) returns zero. -/
noncomputable def observedTruthNorm
    (q : ℕ → T.CompleteType Empty) (N : ℕ)
    (φ : L[[Empty]].Sentence) : ℝ := by
  classical
  exact if ∃ j : ℕ, j < N ∧ φ ∈ q j then 1 else 0

/-- Density detects a fixed nonempty clopen sentence locus at some
finite index and hence at every subsequent finite prefix. -/
theorem denseManifestation_eventually_detects
    (q : ℕ → T.CompleteType Empty) (hq : DenseRange q)
    (φ : L[[Empty]].Sentence) (hφ : (T.typesWith φ).Nonempty) :
    ∃ N : ℕ, ∀ K ≥ N, ∃ j : ℕ, j < K ∧ φ ∈ q j := by
  obtain ⟨j, hj⟩ := hq.exists_mem_open
    (Neoplatonic.LTR.locus_isClopen (T := T) (α := Empty) φ).2 hφ
  refine ⟨j + 1, ?_⟩
  intro K hK
  exact ⟨j, Nat.lt_of_lt_of_le (Nat.lt_succ_self j) hK, hj⟩

/-- Every fixed sentence projection eventually has exactly its true
full C(X,C) norm under finite prefix sampling of a dense sequence. -/
theorem observedTruthNorm_eventually_exact
    (q : ℕ → T.CompleteType Empty) (hq : DenseRange q)
    (φ : L[[Empty]].Sentence) :
    ∃ N : ℕ, ∀ K ≥ N,
      observedTruthNorm q K φ =
        ‖Neoplatonic.LTR.complexLogicalProjection (T := T) φ‖ := by
  classical
  by_cases hφ : (T.typesWith φ).Nonempty
  · obtain ⟨N, hN⟩ :=
      denseManifestation_eventually_detects q hq φ hφ
    have hnorm :
        ‖Neoplatonic.LTR.complexLogicalProjection (T := T) φ‖ = 1 := by
      rw [Neoplatonic.LTR.complexLogicalProjection_norm_eq_real]
      exact Neoplatonic.LTR.logicalProjection_norm_one_of_nonempty φ hφ
    refine ⟨N, ?_⟩
    intro K hK
    obtain ⟨j, hj, hmem⟩ := hN K hK
    have hd : ∃ j : ℕ, j < K ∧ φ ∈ q j :=
      ⟨j, hj, hmem⟩
    simp [observedTruthNorm, hd, hnorm]
  · have hempty : T.typesWith φ = ∅ := by
      ext p
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hp
      exact hφ ⟨p, hp⟩
    have hnorm :
        ‖Neoplatonic.LTR.complexLogicalProjection (T := T) φ‖ = 0 := by
      rw [Neoplatonic.LTR.complexLogicalProjection_norm_eq_real]
      exact (Neoplatonic.LTR.logicalProjection_norm_zero_iff φ).mpr hempty
    refine ⟨0, ?_⟩
    intro K _
    have hd : ¬ ∃ j : ℕ, j < K ∧ φ ∈ q j := by
      rintro ⟨j, _, hmem⟩
      exact hφ ⟨q j, hmem⟩
    simp [observedTruthNorm, hd, hnorm]

/-- Uniform one-sided numerical error is bounded by one because
both logical-projection norms and detection norms lie in [0,1]. -/
theorem observedTruthNorm_error_le_one
    (q : ℕ → T.CompleteType Empty) (N : ℕ)
    (φ : L[[Empty]].Sentence) :
    |observedTruthNorm q N φ -
      ‖Neoplatonic.LTR.complexLogicalProjection (T := T) φ‖| ≤ 1 := by
  classical
  have hge : 0 ≤
      ‖Neoplatonic.LTR.complexLogicalProjection (T := T) φ‖ :=
    norm_nonneg _
  have hle :
      ‖Neoplatonic.LTR.complexLogicalProjection (T := T) φ‖ ≤ 1 := by
    rw [Neoplatonic.LTR.complexLogicalProjection_norm_eq_real]
    exact Neoplatonic.LTR.logicalProjection_norm_le_one φ
  by_cases hd : ∃ j : ℕ, j < N ∧ φ ∈ q j
  · have hv : observedTruthNorm q N φ = 1 := by
      simp [observedTruthNorm, hd]
    rw [hv]
    apply abs_le.mpr
    constructor <;> linarith
  · have hv : observedTruthNorm q N φ = 0 := by
      simp [observedTruthNorm, hd]
    rw [hv]
    apply abs_le.mpr
    constructor <;> linarith

/-- At every finite prefix an explicitly named first-order sentence
has a norm-one full observable but is undetected by the sample. -/
theorem observedTruthNorm_maximum_gap
    (q : ℕ → T.CompleteType Empty) (N : ℕ) :
    ∃ φ : L[[Empty]].Sentence,
      observedTruthNorm q N φ = 0 ∧
      ‖Neoplatonic.LTR.complexLogicalProjection (T := T) φ‖ = 1 := by
  let samples : Fin N → T.CompleteType Empty := fun i => q i.val
  refine ⟨manifestationSentence N samples, ?_,
    manifestationSentence_complex_norm_one N samples⟩
  have hnone :
      ¬ ∃ j : ℕ, j < N ∧ manifestationSentence N samples ∈ q j := by
    rintro ⟨j, hj, hmem⟩
    exact manifestationSentence_samples_false N samples ⟨j, hj⟩ hmem
  simp [observedTruthNorm, hnone]

/-- The worst-case finite-prefix error is exactly one at every depth:
we give both the universal upper bound and an attaining sentence. -/
theorem observedTruthNorm_exact_uniform_gap
    (q : ℕ → T.CompleteType Empty) (N : ℕ) :
    (∀ φ : L[[Empty]].Sentence,
      |observedTruthNorm q N φ -
        ‖Neoplatonic.LTR.complexLogicalProjection (T := T) φ‖| ≤ 1) ∧
    (∃ φ : L[[Empty]].Sentence,
      |observedTruthNorm q N φ -
        ‖Neoplatonic.LTR.complexLogicalProjection (T := T) φ‖| = 1) := by
  constructor
  · intro φ
    exact observedTruthNorm_error_le_one q N φ
  · obtain ⟨φ, hzero, hone⟩ := observedTruthNorm_maximum_gap q N
    refine ⟨φ, ?_⟩
    rw [hzero, hone]
    norm_num

end Neoplatonic.LTR.Nullary
