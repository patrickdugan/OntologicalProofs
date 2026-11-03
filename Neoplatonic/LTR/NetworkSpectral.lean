import Neoplatonic.LTR.ConservativeSpectral

/-!
# Full compact-network spectral conservation theorem

A family of closed compatibility constraints is imposed on a compact
ambient product of local completion spaces. The finite-extension
hypothesis guarantees that every local state can be extended to a
globally compatible family. The compatible subspace is compact, and
its local projection is a continuous surjection.

Therefore every continuous observable of a local system, including
all first-order truth projections, preserves its exact sup norm when
pulled back to the global network. This is a quantitative strengthening
of the earlier coverage/emptiness preservation in Network.lean.

Finite Lipschitz distortion is a separate additional hypothesis.
-/

namespace Neoplatonic.LTR

open Set

universe u v w

/-- Conservative finite-extension gluing induces an isometric pullback
on the uniform norms of continuous real-valued observables. -/
theorem compact_network_preserves_observable_norm
    {X : Type u} {Y : Type v} {K : Type w}
    [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
    (C : K → Set X) (hclosed : ∀ k, IsClosed (C k))
    (f : X → Y) (hf : Continuous f)
    (hfinite : ∀ y : Y, ∀ s : Finset K,
       ∃ x : X, f x = y ∧ ∀ k ∈ s, x ∈ C k)
    (a : C(Y, ℝ)) :
    ‖a.comp
        ⟨(fun z : {x : X // ∀ k, x ∈ C k} => f z.val),
          hf.comp continuous_subtype_val⟩‖ = ‖a‖ := by
  have hZ : IsClosed {x : X | ∀ k, x ∈ C k} := by
    have hz_eq : {x : X | ∀ k, x ∈ C k} = ⋂ k, C k := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [hz_eq]
    exact isClosed_iInter hclosed
  letI : CompactSpace {x : X // ∀ k, x ∈ C k} :=
    isCompact_iff_compactSpace.mp hZ.isCompact
  let g : C({x : X // ∀ k, x ∈ C k}, Y) :=
    ⟨(fun z => f z.val), hf.comp continuous_subtype_val⟩
  have hg : Function.Surjective g :=
    projection_surjective_of_finite_extension C hclosed f hf hfinite
  exact continuous_surjection_preserves_norm g hg a

end Neoplatonic.LTR
