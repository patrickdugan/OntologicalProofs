import Mathlib

/-!
# LTR-02: compact constraint networks

The ambient space can be a product of local completion spaces. Each closed
constraint specifies compatibility along an interpretation or shared interface.
The compactness assumptions are explicit. This file proves finite-to-global
extension, including a fixed local state, and the exact surjectivity criterion
for preserving all truth-locus coverage tests.

Individual edge surjectivity is insufficient; see `Obstruction.lean`.
-/

namespace Neoplatonic.LTR

open Set

universe u v w

/-- All closed constraints in a compact ambient space can be met together
when every finite subfamily can be met together, including the empty family. -/
theorem compact_realization
    {X : Type u} {K : Type v} [TopologicalSpace X] [CompactSpace X]
    (C : K → Set X) (hclosed : ∀ k, IsClosed (C k))
    (hfinite : ∀ s : Finset K, ∃ x : X, ∀ k ∈ s, x ∈ C k) :
    ∃ x : X, ∀ k, x ∈ C k := by
  have hne : (⋂ k, C k).Nonempty :=
    CompactSpace.iInter_nonempty hclosed (by
      intro s
      obtain ⟨x, hx⟩ := hfinite s
      refine ⟨x, ?_⟩
      simpa only [Set.mem_iInter] using hx)
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, by simpa only [Set.mem_iInter] using hx⟩

/-- Inconsistency of a closed compact network always has a finite witness. -/
theorem finite_obstruction
    {X : Type u} {K : Type v} [TopologicalSpace X] [CompactSpace X]
    (C : K → Set X) (hclosed : ∀ k, IsClosed (C k))
    (hglobal : ¬ ∃ x : X, ∀ k, x ∈ C k) :
    ∃ s : Finset K, ¬ ∃ x : X, ∀ k ∈ s, x ∈ C k := by
  classical
  by_contra h
  apply hglobal
  apply compact_realization C hclosed
  intro s
  by_contra hs
  exact h ⟨s, hs⟩

/-- Compatibility along a continuous interpretation is a closed equalizer. -/
theorem transport_constraint_closed
    {I : Type u} {S : I → Type v}
    [∀ i, TopologicalSpace (S i)] {i j : I} [T2Space (S i)]
    (r : S j → S i) (hr : Continuous r) :
    IsClosed {x : ∀ i, S i | x i = r (x j)} := by
  exact isClosed_eq (continuous_apply i) (hr.comp (continuous_apply j))

/-- Prescribing a local state can be included as one further closed constraint.
This is the finite-extension condition needed for a conservative projection. -/
theorem compact_fibre_extension
    {X : Type u} {Y : Type v} {K : Type w}
    [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (C : K → Set X) (hclosed : ∀ k, IsClosed (C k))
    (f : X → Y) (hf : Continuous f) (y : Y)
    (hfinite : ∀ s : Finset K,
      ∃ x : X, f x = y ∧ ∀ k ∈ s, x ∈ C k) :
    ∃ x : X, f x = y ∧ ∀ k, x ∈ C k := by
  classical
  let D : Option K → Set X := fun o =>
    match o with
    | none => {x | f x = y}
    | some k => C k
  have hD : ∀ o, IsClosed (D o) := by
    intro o
    cases o with
    | none => exact isClosed_eq hf continuous_const
    | some k => exact hclosed k
  have hDF : ∀ s : Finset (Option K),
      ∃ x : X, ∀ o ∈ s, x ∈ D o := by
    intro s
    let ks : Finset K := s.biUnion (fun o =>
      match o with
      | none => ∅
      | some k => {k})
    obtain ⟨x, hxy, hx⟩ := hfinite ks
    refine ⟨x, ?_⟩
    intro o ho
    cases o with
    | none => exact hxy
    | some k =>
        apply hx k
        exact Finset.mem_biUnion.mpr ⟨some k, ho, by simp⟩
  obtain ⟨x, hx⟩ := compact_realization D hD hDF
  exact ⟨x, hx none, fun k => hx (some k)⟩

/-- Every local point extends globally under finite extension of that point. -/
theorem projection_surjective_of_finite_extension
    {X : Type u} {Y : Type v} {K : Type w}
    [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (C : K → Set X) (hclosed : ∀ k, IsClosed (C k))
    (f : X → Y) (hf : Continuous f)
    (hfinite : ∀ y : Y, ∀ s : Finset K,
      ∃ x : X, f x = y ∧ ∀ k ∈ s, x ∈ C k) :
    Function.Surjective
      (fun x : {x : X // ∀ k, x ∈ C k} => f x.val) := by
  intro y
  obtain ⟨x, hxy, hx⟩ := compact_fibre_extension C hclosed f hf y (hfinite y)
  exact ⟨⟨x, hx⟩, hxy⟩

/-- A surjective realization preserves and reflects coverage of any locus. -/
theorem cover_pullback_iff
    {X : Type u} {Y : Type v} (f : X → Y)
    (hf : Function.Surjective f) (U : Set Y) :
    f ⁻¹' U = Set.univ ↔ U = Set.univ := by
  constructor
  · intro h
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨x, rfl⟩ := hf y
    have hx : x ∈ f ⁻¹' U := by rw [h]; trivial
    exact hx
  · intro h
    rw [h]
    rfl

/-- A surjective realization preserves and reflects emptiness of any locus. -/
theorem empty_pullback_iff
    {X : Type u} {Y : Type v} (f : X → Y)
    (hf : Function.Surjective f) (U : Set Y) :
    f ⁻¹' U = ∅ ↔ U = ∅ := by
  constructor
  · intro h
    ext y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := hf y
      have hx : x ∈ f ⁻¹' U := hy
      rw [h] at hx
      exact hx
    · intro hy
      exact False.elim hy
  · intro h
    rw [h]
    rfl

/-- Independence survives conservative gluing: both sides of the split survive. -/
theorem nontrivial_pullback_iff
    {X : Type u} {Y : Type v} (f : X → Y)
    (hf : Function.Surjective f) (U : Set Y) :
    (f ⁻¹' U ≠ ∅ ∧ f ⁻¹' U ≠ Set.univ) ↔
      (U ≠ ∅ ∧ U ≠ Set.univ) := by
  simp only [ne_eq, empty_pullback_iff f hf U, cover_pullback_iff f hf U]

/-- Conversely, reflecting coverage for every subset forces surjectivity.
For reflection restricted to clopens, additional Stone-space assumptions are
needed; this theorem deliberately quantifies over all subsets. -/
theorem surjective_iff_reflects_cover
    {X : Type u} {Y : Type v} (f : X → Y) :
    Function.Surjective f ↔
      ∀ U : Set Y, f ⁻¹' U = Set.univ → U = Set.univ := by
  constructor
  · intro hf U h
    exact (cover_pullback_iff f hf U).mp h
  · intro h y
    have hr : f ⁻¹' Set.range f = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      exact ⟨x, rfl⟩
    have hy : y ∈ Set.range f := by rw [h (Set.range f) hr]; trivial
    exact hy

end Neoplatonic.LTR
