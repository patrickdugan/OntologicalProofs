import Neoplatonic.LTR.EffectiveSpectral
import Neoplatonic.LTR.Network

/-!
# Conservative gluing preserves the operator norm of every observable

A continuous surjection of compact spaces induces an exactly
norm-preserving pullback on their continuous real-valued function
algebras. For a conservative interpretation or a finite-extension
compatible network, this means that all labelled truth projections
retain their uniform operator norm, including the exact 0/1
consequence gap.

The norm theorem is independent of metric Lipschitz bounds. Such
bounds require the additional filtration-delay hypotheses of LTR-03.
-/

namespace Neoplatonic.LTR

open FirstOrder
open FirstOrder.Language

universe u v w

/-- Pullback by a continuous surjection is norm-preserving on every
continuous real-valued observable of compact spaces. -/
theorem continuous_surjection_preserves_norm
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y]
    (f : C(X, Y)) (hf : Function.Surjective f) (a : C(Y, ℝ)) :
    ‖a.comp f‖ = ‖a‖ := by
  apply le_antisymm
  · apply (ContinuousMap.norm_le (a.comp f) (norm_nonneg a)).2
    intro x
    simpa only [ContinuousMap.comp_apply] using a.norm_coe_le_norm (f x)
  · apply (ContinuousMap.norm_le a (norm_nonneg (a.comp f))).2
    intro y
    obtain ⟨x, hxy⟩ := hf y
    subst y
    simpa only [ContinuousMap.comp_apply] using
      (a.comp f).norm_coe_le_norm x

/-- In particular, a surjective realization of genuine first-order
complete theories preserves the norm of every logical truth projection. -/
theorem conservative_truth_projection_norm
    {L : FirstOrder.Language.{u, v}} {T : L.Theory}
    {α : Type w} {X : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (f : C(X, T.CompleteType α)) (hf : Function.Surjective f)
    (φ : (L.withConstants α).Sentence) :
    ‖(logicalProjection (T := T) φ).comp f‖ =
      ‖logicalProjection (T := T) φ‖ :=
  continuous_surjection_preserves_norm f hf
    (logicalProjection (T := T) φ)

end Neoplatonic.LTR
