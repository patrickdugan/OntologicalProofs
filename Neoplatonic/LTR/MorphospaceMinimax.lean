import Neoplatonic.LTR.MorphospaceSemiconjugacy
import Mathlib

/-!
# MOR-02: exact fibre-consistency, optimal error obstructions, and composition

This is a deliberately small kernel-checkable component of the wider IDQ-02
minimax autonomy program. No claim about souls, biological minds, or
non-physical causation appears in the theorem statements.
-/

namespace Neoplatonic.LTR.Morphospace

universe u v w t

section Exact

variable {S : Type u} {Z : Type v} {A : Type w}

/-- A surjective state projection admits exact deterministic macro action
maps iff each action gives an unambiguous successor on each fibre. -/
theorem macro_exists_iff_fibre_consistent
    (p : S → Z) (hp : Function.Surjective p) (F : A → S → S) :
    (∃ G : A → Z → Z, ∀ a s, p (F a s) = G a (p s)) ↔
      (∀ a s t, p s = p t → p (F a s) = p (F a t)) := by
  constructor
  · rintro ⟨G, hG⟩ a s t hst
    calc
      p (F a s) = G a (p s) := hG a s
      _ = G a (p t) := by rw [hst]
      _ = p (F a t) := (hG a t).symm
  · intro h
    let sec : Z → S := fun z => Classical.choose (hp z)
    refine ⟨fun a z => p (F a (sec z)), ?_⟩
    intro a s
    exact h a s (sec (p s)) (Classical.choose_spec (hp (p s))).symm

/-- Surjectivity makes the macro action system unique when it exists. -/
theorem macro_unique
    (p : S → Z) (hp : Function.Surjective p) (F : A → S → S)
    (G H : A → Z → Z)
    (hG : ∀ a s, p (F a s) = G a (p s))
    (hH : ∀ a s, p (F a s) = H a (p s)) :
    G = H := by
  funext a z
  obtain ⟨s, rfl⟩ := hp z
  exact (hG a s).symm.trans (hH a s)

end Exact

section Metric

variable {S : Type u} {Y : Type v} {Z : Type w} {A : Type t}
variable [PseudoMetricSpace Y] [PseudoMetricSpace Z]

/-- Two microstates in one fibre with separated projected successors force
large error on at least one of those microstates. -/
theorem fibre_pair_triangle
    (p : S → Y) (F : A → S → S) (G : A → Y → Y)
    (a : A) (s t : S) (hst : p s = p t) :
    dist (p (F a s)) (p (F a t)) ≤
      dist (p (F a s)) (G a (p s)) +
      dist (p (F a t)) (G a (p t)) := by
  calc
    dist (p (F a s)) (p (F a t)) ≤
        dist (p (F a s)) (G a (p s)) +
        dist (G a (p s)) (p (F a t)) := dist_triangle _ _ _
    _ = dist (p (F a s)) (G a (p s)) +
        dist (p (F a t)) (G a (p t)) := by
      rw [hst, dist_comm (G a (p t)) (p (F a t))]

/-- Any single uniform one-step error bound dominates half of every
within-fibre successor diameter. -/
theorem fibre_pair_lower_bound
    (p : S → Y) (F : A → S → S) (G : A → Y → Y)
    (a : A) (s t : S) (hst : p s = p t)
    (eps : ℝ)
    (hs : dist (p (F a s)) (G a (p s)) ≤ eps)
    (ht : dist (p (F a t)) (G a (p t)) ≤ eps) :
    dist (p (F a s)) (p (F a t)) ≤ 2 * eps := by
  have h := fibre_pair_triangle p F G a s t hst
  linarith

/-- One-step errors of approximate quotients compose, with distortion
controlled by the Lipschitz constant of the downstream projection. -/
theorem approximate_quotient_composition
    (p : S → Y) (rho : Y → Z)
    (F : A → S → S) (G : A → Y → Y) (H : A → Z → Z)
    (L eps₁ eps₂ : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y y', dist (rho y) (rho y') ≤ L * dist y y')
    (hFirst : ∀ a s, dist (p (F a s)) (G a (p s)) ≤ eps₁)
    (hSecond : ∀ a y, dist (rho (G a y)) (H a (rho y)) ≤ eps₂)
    (a : A) (s : S) :
    dist (rho (p (F a s))) (H a (rho (p s))) ≤
      L * eps₁ + eps₂ := by
  calc
    dist (rho (p (F a s))) (H a (rho (p s))) ≤
        dist (rho (p (F a s))) (rho (G a (p s))) +
        dist (rho (G a (p s))) (H a (rho (p s))) :=
          dist_triangle _ _ _
    _ ≤ L * dist (p (F a s)) (G a (p s)) + eps₂ :=
      add_le_add (hLip _ _) (hSecond a (p s))
    _ ≤ L * eps₁ + eps₂ :=
      add_le_add_right (mul_le_mul_of_nonneg_left (hFirst a s) hL) _

end Metric

end Neoplatonic.LTR.Morphospace
