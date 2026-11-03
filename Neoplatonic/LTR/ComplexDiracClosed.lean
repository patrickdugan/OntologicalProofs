import Neoplatonic.LTR.ComplexDiracDomain
import Mathlib.Topology.Algebra.Module.LinearPMap

/-!
# Closed graph of the maximal complex block Dirac operator

The graph is precisely the set of (ψ,η) whose coordinates satisfy
η_j = D_j ψ_j. Each coordinate equality is closed; the intersection
is closed. The maximal domain makes the coordinate graph exact.
-/

namespace Neoplatonic.LTR

/-- Characterization of the maximal complex Dirac graph by all block equations. -/
theorem maximalComplexDiracPMap_graph_eq
    (mass scale : ℕ → ℝ) :
    ((maximalComplexDiracPMap mass scale).graph :
       Set (ComplexDiracBlockHilbert × ComplexDiracBlockHilbert)) =
    {p | ∀ j : ℕ, p.2 j =
      complexEuclideanDiracBlock (mass j) (scale j) (p.1 j)} := by
  ext p
  constructor
  · intro hp j
    obtain ⟨x, hx, hy⟩ :=
      (LinearPMap.mem_graph_iff (maximalComplexDiracPMap mass scale)).mp hp
    have heval := congrArg
      (fun z : ComplexDiracBlockHilbert => z j) hy
    have hblock :
        ((maximalComplexDiracPMap mass scale) x) j =
          complexEuclideanDiracBlock (mass j) (scale j)
            ((x : ComplexDiracBlockHilbert) j) := rfl
    rw [← heval, hblock, hx]
  · intro hp
    have hmem : p.1 ∈ maximalComplexDiracDomain mass scale := by
      change Memℓp (complexDiracBlockwise mass scale p.1) 2
      have heq : complexDiracBlockwise mass scale p.1 =
          (p.2 : ℕ → EuclideanSpace ℂ (Fin 2)) := by
        funext j
        exact (hp j).symm
      rw [heq]
      exact lp.memℓp p.2
    apply (LinearPMap.mem_graph_iff (maximalComplexDiracPMap mass scale)).mpr
    refine ⟨⟨p.1, hmem⟩, rfl, ?_⟩
    apply lp.ext
    funext j
    exact (hp j).symm

/-- The maximal complex Dirac linear partial map is closed. -/
theorem maximalComplexDiracPMap_isClosed
    (mass scale : ℕ → ℝ) :
    (maximalComplexDiracPMap mass scale).IsClosed := by
  change IsClosed
    ((maximalComplexDiracPMap mass scale).graph :
      Set (ComplexDiracBlockHilbert × ComplexDiracBlockHilbert))
  rw [maximalComplexDiracPMap_graph_eq]
  have heq :
      {p : ComplexDiracBlockHilbert × ComplexDiracBlockHilbert |
        ∀ j : ℕ, p.2 j =
          complexEuclideanDiracBlock (mass j) (scale j) (p.1 j)} =
      ⋂ j : ℕ, {p : ComplexDiracBlockHilbert × ComplexDiracBlockHilbert |
        p.2 j =
          complexEuclideanDiracBlock (mass j) (scale j) (p.1 j)} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
  rw [heq]
  apply isClosed_iInter
  intro j
  apply isClosed_eq
  · exact (lp.evalCLM ℂ (fun _ : ℕ =>
        EuclideanSpace ℂ (Fin 2)) 2 j).continuous.comp continuous_snd
  · exact (complexEuclideanDiracBlock (mass j) (scale j)).continuous.comp
      ((lp.evalCLM ℂ (fun _ : ℕ =>
        EuclideanSpace ℂ (Fin 2)) 2 j).continuous.comp continuous_fst)

end Neoplatonic.LTR
