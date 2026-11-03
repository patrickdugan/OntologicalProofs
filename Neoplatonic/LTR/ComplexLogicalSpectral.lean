import Neoplatonic.LTR.LogicalSpectral
import Mathlib.Topology.ContinuousMap.Star

/-!
# Complex C*-algebra realization of first-order sentence projections

The real-valued Stone truth projection extends canonically to a
complex-valued continuous observable. This is a self-adjoint
idempotent in the commutative C*-algebra C(X_T, Complex).
Its C*-norm is equal to the real sup norm already checked in
LogicalSpectral.lean. Therefore its refutation norm detects
semantic entailment by the same strict zero/one gap.

This fixes the operator algebra's conventional scalar field,
while remaining independent of the infinite unbounded Dirac
domain and its spectral analysis.
-/

namespace Neoplatonic.LTR

open FirstOrder
open FirstOrder.Language

universe u v w
variable {L : FirstOrder.Language.{u, v}} {T : L.Theory} {α : Type w}

/-- Genuine complex-valued truth projection on the Stone completion space. -/
noncomputable def complexLogicalProjection
    (φ : (L.withConstants α).Sentence) : C(T.CompleteType α, ℂ) :=
  ⟨fun p => ((logicalProjection (T := T) φ p : ℝ) : ℂ),
    Complex.continuous_ofReal.comp
      (logicalProjection (T := T) φ).continuous⟩

theorem complexLogicalProjection_apply_mem
    (φ : (L.withConstants α).Sentence)
    (p : T.CompleteType α) (h : φ ∈ p) :
    complexLogicalProjection (T := T) φ p = 1 := by
  change ((logicalProjection (T := T) φ p : ℝ) : ℂ) = 1
  rw [logicalProjection_apply_mem (T := T) φ p h]
  norm_num

theorem complexLogicalProjection_apply_not_mem
    (φ : (L.withConstants α).Sentence)
    (p : T.CompleteType α) (h : φ ∉ p) :
    complexLogicalProjection (T := T) φ p = 0 := by
  change ((logicalProjection (T := T) φ p : ℝ) : ℂ) = 0
  rw [logicalProjection_apply_not_mem (T := T) φ p h]
  norm_num

/-- Logical truth is represented by an idempotent in the complex algebra. -/
theorem complexLogicalProjection_idempotent
    (φ : (L.withConstants α).Sentence) :
    complexLogicalProjection (T := T) φ *
      complexLogicalProjection (T := T) φ =
    complexLogicalProjection (T := T) φ := by
  ext p
  by_cases hp : φ ∈ p
  · simp [complexLogicalProjection_apply_mem (T := T) φ p hp]
  · simp [complexLogicalProjection_apply_not_mem (T := T) φ p hp]

/-- Its adjoint is itself, making the idempotent a C*-projection. -/
theorem complexLogicalProjection_selfadjoint
    (φ : (L.withConstants α).Sentence) :
    star (complexLogicalProjection (T := T) φ) =
      complexLogicalProjection (T := T) φ := by
  ext p
  by_cases hp : φ ∈ p
  · simp [ContinuousMap.star_apply,
      complexLogicalProjection_apply_mem (T := T) φ p hp]
  · simp [ContinuousMap.star_apply,
      complexLogicalProjection_apply_not_mem (T := T) φ p hp]

/-- Complexification preserves exactly the uniform observable norm. -/
theorem complexLogicalProjection_norm_eq_real
    (φ : (L.withConstants α).Sentence) :
    ‖complexLogicalProjection (T := T) φ‖ =
      ‖logicalProjection (T := T) φ‖ := by
  simp only [ContinuousMap.norm_eq_iSup_norm,
    complexLogicalProjection, ContinuousMap.coe_mk,
    Complex.norm_real, Real.norm_eq_abs]

/-- The complex C*-algebra norm detects first-order semantic consequence. -/
theorem complex_refutation_norm_zero_iff_entails
    (φ : (L.withConstants α).Sentence) :
    ‖complexLogicalProjection (T := T) φ.not‖ = 0 ↔
      (L.lhomWithConstants α).onTheory T ⊨ᵇ φ := by
  rw [complexLogicalProjection_norm_eq_real]
  exact refutation_norm_zero_iff_entails (T := T) φ

end Neoplatonic.LTR
