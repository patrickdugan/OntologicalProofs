import Mathlib
import Neoplatonic.LocalConfluence

/-!
# Logos -> Topos: conditional local-to-global and curvature lemmas

All mathematical claims here are conditional. `ConfluentGroundTheory` proves
uniqueness of an ontological root within the asserted priority relation.
The `Atlas` and `ClosedTriCounts` constructions supply mathematical analogies;
no theorem identifies these structures with God, divine attributes, or reality.
-/

namespace Neoplatonic.LogosTopos

universe u v w

/-- Pointwise local data, carried over overlapping contexts. This is a
finite-dimensional proxy for sheaf gluing, rather than a sheaf on a site. -/
structure Atlas (X : Type u) (I : Type v) (A : Type w) where
  covers : I → X → Prop
  localValue : I → X → A
  covered : ∀ x, ∃ i, covers i x
  overlap : ∀ i j x, covers i x → covers j x → localValue i x = localValue j x

/-- An Alexandrov-style open subset of the reachability preorder:
    membership is upward closed along grounding/manifestation. -/
def GroundUpwardClosed {α : Type u}
    (prior : α → α → Prop) (U : Set α) : Prop :=
  ∀ x y : α, x ∈ U → Reach prior x y → y ∈ U

/-- Universal grounding is exactly the statement that every upward-closed
    open context containing the origin covers every form. -/
theorem universal_origin_iff_open_saturation {α : Type u}
    (prior : α → α → Prop) (g : α) :
    (∀ x : α, Reach prior g x) ↔
      (∀ U : Set α, GroundUpwardClosed prior U →
        g ∈ U → U = Set.univ) := by
  constructor
  · intro hg U hOpen hgU
    ext x
    simp only [Set.mem_univ, iff_true]
    exact hOpen g x hgU (hg x)
  · intro hAll x
    let U : Set α := {y | Reach prior g y}
    have hOpen : GroundUpwardClosed prior U := by
      intro a b ha hab
      exact reach_trans ha hab
    have heq : U = Set.univ := hAll U hOpen (Reach.refl g)
    have hx : x ∈ U := by rw [heq]; trivial
    exact hx

/-- The unique first principle saturates all of its upward-open contexts. -/
theorem first_principle_saturates_open {α : Type u}
    {prior : α → α → Prop} {g : α}
    (hg : FirstPrinciple prior g) :
    ∀ U : Set α, GroundUpwardClosed prior U →
      g ∈ U → U = Set.univ :=
  (universal_origin_iff_open_saturation prior g).mp hg.2

namespace Atlas

variable {X : Type u} {I : Type v} {A : Type w}

noncomputable def glued (D : Atlas X I A) (x : X) : A :=
  D.localValue (Classical.choose (D.covered x)) x

theorem glued_agrees (D : Atlas X I A) (i : I) (x : X)
    (hx : D.covers i x) : glued D x = D.localValue i x := by
  unfold glued
  exact D.overlap _ i x (Classical.choose_spec (D.covered x)) hx

theorem unique_gluing (D : Atlas X I A) :
    ∃! g : X → A, ∀ i x, D.covers i x → g x = D.localValue i x := by
  refine ⟨glued D, ?_, ?_⟩
  · intro i x hx
    exact glued_agrees D i x hx
  · intro g hg
    funext x
    obtain ⟨i, hx⟩ := D.covered x
    exact (hg i x hx).trans (glued_agrees D i x hx).symm

end Atlas

/-- Incidence-count certificate of a closed triangular cellulation.
`handshake` and `triangles` must be derived from actual incidence data
in a later layer rather than simply assumed for concrete examples. -/
structure ClosedTriCounts (V : Type*) [Fintype V] where
  degree : V → ℕ
  edges : ℕ
  faces : ℕ
  handshake : (∑ v : V, (degree v : ℤ)) = 2 * (edges : ℤ)
  triangles : 3 * (faces : ℤ) = 2 * (edges : ℤ)

def euler {V : Type*} [Fintype V] (T : ClosedTriCounts V) : ℤ :=
  (Fintype.card V : ℤ) - (T.edges : ℤ) + (T.faces : ℤ)

def defect {V : Type*} [Fintype V] (T : ClosedTriCounts V) (v : V) : ℤ :=
  6 - (T.degree v : ℤ)

/-- A discrete Gauss-Bonnet-style identity: summed degree defect = 6 Euler.
The curvature unit `6 - degree` equals 6 times the usual normalized
combinatorial curvature `(1 - degree / 6)`. -/
theorem discrete_gauss_bonnet {V : Type*} [Fintype V]
    (T : ClosedTriCounts V) :
    (∑ v : V, defect T v) = 6 * euler T := by
  classical
  have hsum :
      (∑ v : V, defect T v) =
        6 * (Fintype.card V : ℤ) - (∑ v : V, (T.degree v : ℤ)) := by
    simp [defect, Finset.sum_sub_distrib, mul_comm]
  rw [hsum, T.handshake]
  have ht := T.triangles
  unfold euler
  omega

/-- The sum of a symmetric-weights graph Laplacian vanishes. -/
theorem total_divergence_zero {V : Type*} [Fintype V]
    (weight : V → V → ℤ)
    (symmetric : ∀ v u, weight v u = weight u v)
    (potential : V → ℤ) :
    (∑ v : V, ∑ u : V,
      weight v u * (potential v - potential u)) = 0 := by
  classical
  have hswap :
      (∑ v : V, ∑ u : V, weight v u * potential v) =
      (∑ v : V, ∑ u : V, weight v u * potential u) := by
    calc
      (∑ v : V, ∑ u : V, weight v u * potential v) =
          ∑ u : V, ∑ v : V, weight v u * potential v := by
        rw [Finset.sum_comm]
      _ = ∑ u : V, ∑ v : V, weight u v * potential v := by
        apply Finset.sum_congr rfl
        intro u _
        apply Finset.sum_congr rfl
        intro v _
        rw [symmetric v u]
      _ = ∑ v : V, ∑ u : V, weight v u * potential u := rfl
  calc
    (∑ v : V, ∑ u : V,
      weight v u * (potential v - potential u)) =
        (∑ v : V, ∑ u : V, weight v u * potential v) -
        (∑ v : V, ∑ u : V, weight v u * potential u) := by
          simp only [mul_sub, Finset.sum_sub_distrib]
    _ = 0 := sub_eq_zero.mpr hswap

/-- The finite weighted graph Laplacian, with an explicit vertex parameter
so the nested binder has a fixed type before summation elaboration. -/
def graphLaplacian {V : Type*} [Fintype V]
    (weight : V → V → ℤ) (potential : V → ℤ) (v : V) : ℤ :=
  ∑ u : V, weight v u * (potential v - potential u)

/-- Potential-driven redistribution preserves total curvature. -/
theorem total_curvature_stable {V : Type*} [Fintype V]
    (K : V → ℤ) (weight : V → V → ℤ)
    (symmetric : ∀ v u, weight v u = weight u v)
    (potential : V → ℤ) :
    (Finset.univ.sum (fun v : V => K v - graphLaplacian weight potential v)) =
    (Finset.univ.sum (fun v : V => K v)) := by
  classical
  have hsum :
      (Finset.univ.sum (fun v : V => graphLaplacian weight potential v)) = 0 := by
    simpa only [graphLaplacian] using
      (total_divergence_zero weight symmetric potential)
  rw [Finset.sum_sub_distrib, hsum]
  ring

/-- The curvature of a closed triangulation has a fixed global total
under any symmetric potential redistribution. -/
theorem potential_preserves_euler {V : Type*} [Fintype V]
    (T : ClosedTriCounts V) (weight : V → V → ℤ)
    (symmetric : ∀ v u, weight v u = weight u v)
    (potential : V → ℤ) :
    (Finset.univ.sum (fun v : V =>
      defect T v - graphLaplacian weight potential v)) =
      6 * euler T := by
  calc
    (Finset.univ.sum (fun v : V =>
      defect T v - graphLaplacian weight potential v)) =
      (Finset.univ.sum (fun v : V => defect T v)) :=
        total_curvature_stable (defect T) weight symmetric potential
    _ = 6 * euler T := discrete_gauss_bonnet T

/-- A three-step transport loop that translates by +1 has no
simultaneously compatible integral global parallel value. -/
theorem translation_holonomy_obstruction :
    ¬ ∃ x₀ x₁ x₂ : ℤ,
       x₁ = x₀ + 1 ∧ x₂ = x₁ + 1 ∧ x₀ = x₂ + 1 := by
  rintro ⟨x₀, x₁, x₂, h₁, h₂, h₃⟩
  omega

/-- Existence of one ontological root permits many distinct maps/forms.
This is the explicit countermodel to the unwarranted uniqueness leap. -/
theorem one_ground_many_forms :
    (∃! root : ℕ, FirstPrinciple natTheory.prior root) ∧
      (∃ f g : Unit → Bool, f ≠ g) := by
  constructor
  · exact zero_is_unique_first_principle
  · refine ⟨(fun _ => true), (fun _ => false), ?_⟩
    intro h
    have hval := congrFun h ()
    cases hval

end Neoplatonic.LogosTopos
