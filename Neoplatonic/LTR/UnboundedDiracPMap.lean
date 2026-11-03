import Neoplatonic.LTR.BoundedHilbertDiagonal
import Neoplatonic.LTR.SpectralBridge
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Maximal domain of the infinite Dirac operator

Each two-component Euclidean Hilbert block carries the genuine
continuous linear operator corresponding to the symmetric matrix

  D_j = [[m_j,s_j],[s_j,-m_j]].

The maximal domain in H=ℓ²(ℕ,ℝ²) consists of all Hilbert vectors ψ
whose pointwise blockwise images D_j ψ_j are square-summable.

This file constructs the domain as a *Submodule ℝ H* and the resulting
densely definable *LinearPMap* (an unbounded linear operator in
mathlib). The domain choice is explicit. Formal self-adjointness and
closed graph must be proved separately on this maximal domain.

No unproved continuity, closedness, or self-adjointness theorem is
assumed in these definitions.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- The genuine finite-dimensional bounded Dirac block on ℝ². -/
noncomputable def euclideanDiracBlock (mass scale : ℝ) :
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Matrix.toEuclideanCLM (massDirac mass scale)

/-- Blockwise action of an arbitrary mass/scale sequence on an ℓ² vector,
viewed as a function of blocks before square-summability is imposed. -/
noncomputable def diracBlockwise (mass scale : ℕ → ℝ)
    (ψ : DiracBlockHilbert) : ℕ → EuclideanSpace ℝ (Fin 2) :=
  fun j => euclideanDiracBlock (mass j) (scale j) (ψ j)

/-- The maximal square-summable domain of the unbounded Dirac action. -/
noncomputable def maximalDiracDomain (mass scale : ℕ → ℝ) :
    Submodule ℝ DiracBlockHilbert where
  carrier := {ψ | Memℓp (diracBlockwise mass scale ψ) 2}
  zero_mem' := by
    change Memℓp (diracBlockwise mass scale (0 : DiracBlockHilbert)) 2
    have hz : diracBlockwise mass scale (0 : DiracBlockHilbert) =
        fun _ => (0 : EuclideanSpace ℝ (Fin 2)) := by
      funext j
      simp [diracBlockwise]
    rw [hz]
    exact lp.zero_mem_ℓp'
  add_mem' := by
    intro x y hx hy
    change Memℓp (diracBlockwise mass scale (x + y)) 2
    have hxy : diracBlockwise mass scale (x + y) =
        diracBlockwise mass scale x + diracBlockwise mass scale y := by
      funext j
      simp only [diracBlockwise, Pi.add_apply, lp.coeFn_add]
      exact (euclideanDiracBlock (mass j) (scale j)).map_add (x j) (y j)
    rw [hxy]
    exact Memℓp.add hx hy
  smul_mem' := by
    intro r x hx
    change Memℓp (diracBlockwise mass scale (r • x)) 2
    have hr : diracBlockwise mass scale (r • x) =
        r • diracBlockwise mass scale x := by
      funext j
      simp only [diracBlockwise, Pi.smul_apply, lp.coeFn_smul]
      exact (euclideanDiracBlock (mass j) (scale j)).map_smul r (x j)
    rw [hr]
    exact Memℓp.const_smul hx r

/-- The maximal-domain unbounded Dirac operator, as an actual mathlib
partially defined linear map on the infinite Hilbert sum. -/
noncomputable def maximalDiracPMap (mass scale : ℕ → ℝ) :
    DiracBlockHilbert →ₗ.[ℝ] DiracBlockHilbert where
  domain := maximalDiracDomain mass scale
  toFun :=
    { toFun := fun ψ =>
        ⟨diracBlockwise mass scale (ψ : DiracBlockHilbert), ψ.property⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext j
        exact (euclideanDiracBlock (mass j) (scale j)).map_add (x.val j) (y.val j)
      map_smul' := by
        intro r x
        apply lp.ext
        funext j
        exact (euclideanDiracBlock (mass j) (scale j)).map_smul r (x.val j) }

/-- The unbounded map's domain is exactly the square-summable block
image condition; no implicit enlargement of the domain occurs. -/
theorem maximalDiracPMap_domain (mass scale : ℕ → ℝ) :
    (maximalDiracPMap mass scale).domain =
      maximalDiracDomain mass scale := rfl

end Neoplatonic.LTR
