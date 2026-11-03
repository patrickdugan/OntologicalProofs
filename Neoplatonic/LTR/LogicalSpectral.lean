import Neoplatonic.LTR.Stone
import Neoplatonic.LTR.SpectralBridge
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Algebra.Indicator

/-!
# LTR-06: logical clopen projections inside the continuous-function algebra

Every sentence of a genuine first-order theory determines an idempotent
real-valued continuous observable on its Stone space of complete types.
The projection has sup norm exactly 0 or 1. In particular, the norm of
the *refutation* projection is zero precisely when the sentence follows
from the theory.

The results hold for arbitrary first-order theories and their actual
mathlib CompleteType spaces. The proof uses no assumed decision oracle.
The representation by continuous functions is commutative and faithful;
the finite spectral Dirac commutator is treated in a separate theorem.

For complex-valued C*-algebra operators, base change from real to complex
requires a separate explicit step. This file makes no claim to have
formalized the unbounded infinite direct-sum Dirac domain.
-/

namespace Neoplatonic.LTR

open FirstOrder Set
open FirstOrder.Language

universe u v w

variable {L : FirstOrder.Language.{u, v}} {T : L.Theory} {α : Type w}

/-- The characteristic function of a sentence's clopen truth locus.
It is a genuine continuous real-valued observable on the completion space. -/
noncomputable def logicalProjection
    (φ : (L.withConstants α).Sentence) : C(T.CompleteType α, ℝ) :=
  ⟨(T.typesWith φ).indicator (fun _ => (1 : ℝ)),
    (locus_isClopen (T := T) (α := α) φ).continuous_indicator continuous_const⟩

/-- At a completion containing the sentence, its observable has value 1. -/
theorem logicalProjection_apply_mem
    (φ : (L.withConstants α).Sentence) (p : T.CompleteType α)
    (h : φ ∈ p) : logicalProjection φ p = 1 := by
  simp [logicalProjection, FirstOrder.Language.Theory.typesWith, h]

/-- At a completion refuting the sentence, its observable has value 0. -/
theorem logicalProjection_apply_not_mem
    (φ : (L.withConstants α).Sentence) (p : T.CompleteType α)
    (h : φ ∉ p) : logicalProjection φ p = 0 := by
  simp [logicalProjection, FirstOrder.Language.Theory.typesWith, h]

/-- The logical truth observable is an idempotent in the function algebra. -/
theorem logicalProjection_idempotent
    (φ : (L.withConstants α).Sentence) :
    logicalProjection φ * logicalProjection φ = logicalProjection φ := by
  ext p
  by_cases hp : φ ∈ p
  · simp [logicalProjection_apply_mem φ p hp]
  · simp [logicalProjection_apply_not_mem φ p hp]

/-- An idempotent truth observable has norm at most one. -/
theorem logicalProjection_norm_le_one
    (φ : (L.withConstants α).Sentence) :
    ‖logicalProjection φ‖ ≤ 1 := by
  apply (ContinuousMap.norm_le _ (by norm_num)).2
  intro p
  by_cases hp : φ ∈ p
  · simp [logicalProjection_apply_mem φ p hp]
  · simp [logicalProjection_apply_not_mem φ p hp]

/-- If the sentence holds at any complete theory, its norm is exactly one. -/
theorem logicalProjection_norm_one_of_nonempty
    (φ : (L.withConstants α).Sentence)
    (h : (T.typesWith φ).Nonempty) :
    ‖logicalProjection φ‖ = 1 := by
  obtain ⟨p, hp⟩ := h
  apply le_antisymm (logicalProjection_norm_le_one φ)
  have hbound := (logicalProjection φ).norm_coe_le_norm p
  have hmem : φ ∈ p := hp
  simpa [logicalProjection_apply_mem φ p hmem] using hbound

/-- Empty truth locus makes the continuous observable identically zero. -/
theorem logicalProjection_eq_zero_of_empty
    (φ : (L.withConstants α).Sentence)
    (h : T.typesWith φ = ∅) : logicalProjection φ = 0 := by
  ext p
  have hp : φ ∉ p := by
    intro hφ
    have : p ∈ T.typesWith φ := hφ
    rw [h] at this
    exact this
  simp [logicalProjection_apply_not_mem φ p hp]

/-- The observable norm is zero precisely when the truth locus is empty. -/
theorem logicalProjection_norm_zero_iff
    (φ : (L.withConstants α).Sentence) :
    ‖logicalProjection φ‖ = 0 ↔ T.typesWith φ = ∅ := by
  constructor
  · intro hnorm
    by_contra hne
    have hnonempty : (T.typesWith φ).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hne
    have hone := logicalProjection_norm_one_of_nonempty φ hnonempty
    rw [hnorm] at hone
    norm_num at hone
  · intro h
    rw [logicalProjection_eq_zero_of_empty φ h]
    exact norm_zero

/-- Refutation-projector norm 0 is equivalent to semantic consequence.
The sentence code and its geometric observable have an explicit identity
reduction; no computation of a complete theory is assumed. -/
theorem refutation_norm_zero_iff_entails
    (φ : (L.withConstants α).Sentence) :
    ‖logicalProjection (T := T) φ.not‖ = 0 ↔
      (L.lhomWithConstants α).onTheory T ⊨ᵇ φ := by
  rw [logicalProjection_norm_zero_iff, locus_not]
  rw [Set.compl_eq_empty_iff]
  exact locus_eq_univ (T := T) φ

/-- If the sentence is independent, both its truth and refutation
observables have norm exactly one. -/
theorem independent_norms
    (φ : (L.withConstants α).Sentence) (h : Independent T φ) :
    ‖logicalProjection (T := T) φ‖ = 1 ∧
      ‖logicalProjection (T := T) φ.not‖ = 1 := by
  have hsplit := (independent_iff_nontrivial_locus φ).mp h
  constructor
  · exact logicalProjection_norm_one_of_nonempty φ hsplit.1
  · apply logicalProjection_norm_one_of_nonempty
    rw [locus_not]
    exact Set.nonempty_compl.mpr hsplit.2

end Neoplatonic.LTR
