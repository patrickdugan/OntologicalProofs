import Neoplatonic.LTR.ComplexLogicalSpectral
import Neoplatonic.LTR.NetworkSpectral

/-!
# Exact norm conservation for complex C*-algebra observables

Surjective continuous maps of compact spaces act contravariantly on
commutative unital C*-algebras of complex-valued continuous functions.
Their pullback maps are isometric. In a conservative compact network,
this preserves the norm of every complex logical projection.

The global compatible-space compactness instance is established in
NetworkSpectral.lean and inserted in the statement before the norm
expression is elaborated.
-/

namespace Neoplatonic.LTR

open FirstOrder
open FirstOrder.Language
open Set

universe u v w z

theorem continuous_surjection_preserves_complex_norm
    {X : Type u} {Y : Type v}
    [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y]
    (f : C(X, Y)) (hf : Function.Surjective f) (a : C(Y, ℂ)) :
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

theorem complex_conservative_truth_projection_norm
    {L : FirstOrder.Language.{u, v}} {T : L.Theory}
    {α : Type w} {X : Type z}
    [TopologicalSpace X] [CompactSpace X]
    (f : C(X, T.CompleteType α)) (hf : Function.Surjective f)
    (φ : (L.withConstants α).Sentence) :
    ‖(complexLogicalProjection (T := T) φ).comp f‖ =
      ‖complexLogicalProjection (T := T) φ‖ :=
  continuous_surjection_preserves_complex_norm f hf
    (complexLogicalProjection (T := T) φ)

/-- Conservative finite-extension compatibility implies norm conservation
of every complex sentence projection, directly on the compact global
space of compatible valuations. -/
theorem compact_network_preserves_complex_logical_norm
    {L : FirstOrder.Language.{u, v}} {T : L.Theory}
    {α : Type w} {X : Type z} {K : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (C : K → Set X) (hclosed : ∀ k, IsClosed (C k))
    (f : X → T.CompleteType α) (hf : Continuous f)
    (hfinite : ∀ y : T.CompleteType α, ∀ s : Finset K,
      ∃ x : X, f x = y ∧ ∀ k ∈ s, x ∈ C k)
    (φ : (L.withConstants α).Sentence) :
    (letI : CompactSpace {x : X // ∀ k, x ∈ C k} :=
       compatibleSpaceCompact C hclosed
     ‖(complexLogicalProjection (T := T) φ).comp
       ⟨(fun x : {x : X // ∀ k, x ∈ C k} => f x.val),
         hf.comp continuous_subtype_val⟩‖ =
      ‖complexLogicalProjection (T := T) φ‖) := by
  letI : CompactSpace {x : X // ∀ k, x ∈ C k} :=
    compatibleSpaceCompact C hclosed
  let g : C({x : X // ∀ k, x ∈ C k}, T.CompleteType α) :=
    ⟨(fun x => f x.val), hf.comp continuous_subtype_val⟩
  have hg : Function.Surjective g :=
    projection_surjective_of_finite_extension C hclosed f hf hfinite
  exact complex_conservative_truth_projection_norm g hg φ

end Neoplatonic.LTR
