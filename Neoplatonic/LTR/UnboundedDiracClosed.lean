import Neoplatonic.LTR.UnboundedDiracDense
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Closedness of the maximal-domain infinite Dirac operator

The maximal-domain Dirac operator on H=ℓ²(ℕ,ℝ²) has a graph
characterized by the coordinate equations y_j=D_j x_j.

Every equation cuts out a closed subset of H×H because coordinate
evaluation and the finite-dimensional D_j are continuous. Their
intersection is therefore closed. The equivalence between the
coordinate constraints and the actual partial linear map's graph
uses the maximal-domain definition: a square-summable output vector
provides exactly the domain membership needed.

This proves that the genuine infinite operator is closed, using
mathlib's definition LinearPMap.IsClosed. Symmetry on its maximal
domain and self-adjointness are separate further obligations.
-/

namespace Neoplatonic.LTR

open Set

/-- The graph is exactly the solution set of every block equation. -/
theorem maximalDiracPMap_graph_eq
    (mass scale : ℕ → ℝ) :
    ((maximalDiracPMap mass scale).graph :
       Set (DiracBlockHilbert × DiracBlockHilbert)) =
    {p | ∀ j : ℕ, p.2 j =
      euclideanDiracBlock (mass j) (scale j) (p.1 j)} := by
  ext p
  constructor
  · intro hp j
    obtain ⟨x, hx, hy⟩ :=
      (LinearPMap.mem_graph_iff (maximalDiracPMap mass scale)).mp hp
    have heval := congrArg
      (fun z : DiracBlockHilbert => z j) hy
    have hblock :
        ((maximalDiracPMap mass scale) x) j =
          euclideanDiracBlock (mass j) (scale j) ((x : DiracBlockHilbert) j) :=
      rfl
    rw [← heval, hblock, hx]
  · intro hp
    have hmem : p.1 ∈ maximalDiracDomain mass scale := by
      change Memℓp (diracBlockwise mass scale p.1) 2
      have heq : diracBlockwise mass scale p.1 =
          (p.2 : ℕ → EuclideanSpace ℝ (Fin 2)) := by
        funext j
        exact (hp j).symm
      rw [heq]
      exact lp.memℓp p.2
    apply (LinearPMap.mem_graph_iff (maximalDiracPMap mass scale)).mpr
    refine ⟨⟨p.1, hmem⟩, rfl, ?_⟩
    apply lp.ext
    funext j
    exact (hp j).symm

/-- The maximal-domain Dirac action is a closed unbounded operator. -/
theorem maximalDiracPMap_isClosed
    (mass scale : ℕ → ℝ) :
    (maximalDiracPMap mass scale).IsClosed := by
  change IsClosed
    ((maximalDiracPMap mass scale).graph :
      Set (DiracBlockHilbert × DiracBlockHilbert))
  rw [maximalDiracPMap_graph_eq]
  have heq :
      {p : DiracBlockHilbert × DiracBlockHilbert |
        ∀ j : ℕ, p.2 j =
          euclideanDiracBlock (mass j) (scale j) (p.1 j)} =
      ⋂ j : ℕ, {p : DiracBlockHilbert × DiracBlockHilbert |
        p.2 j =
          euclideanDiracBlock (mass j) (scale j) (p.1 j)} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [heq]
  apply isClosed_iInter
  intro j
  apply isClosed_eq
  · exact (lp.evalCLM ℝ (fun _ : ℕ =>
        EuclideanSpace ℝ (Fin 2)) 2 j).continuous.comp continuous_snd
  · exact (euclideanDiracBlock (mass j) (scale j)).continuous.comp
      ((lp.evalCLM ℝ (fun _ : ℕ =>
        EuclideanSpace ℝ (Fin 2)) 2 j).continuous.comp continuous_fst)

end Neoplatonic.LTR
