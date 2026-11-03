import Neoplatonic.LTR.ComplexDiracClosed
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Self-adjoint maximal Dirac operator on ℓ²(ℕ,ℂ²)

A finite-dimensional Hermitian Dirac block is self-adjoint. The
blockwise sum is formally symmetric. Testing the infinite adjoint
against an arbitrary single-block vector determines every coordinate
of the adjoint and shows that its domain is contained in the maximal
square-summable Dirac domain. This establishes D*=D.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Formal symmetry of the complex direct-sum Dirac operator. -/
theorem maximalComplexDiracPMap_formalSymmetric
    (mass scale : ℕ → ℝ) :
    (maximalComplexDiracPMap mass scale).IsFormalAdjoint
      (maximalComplexDiracPMap mass scale) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro j
  change inner ℂ
      (complexEuclideanDiracBlock (mass j) (scale j)
        ((x : ComplexDiracBlockHilbert) j))
      ((y : ComplexDiracBlockHilbert) j) =
    inner ℂ ((x : ComplexDiracBlockHilbert) j)
      (complexEuclideanDiracBlock (mass j) (scale j)
        ((y : ComplexDiracBlockHilbert) j))
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (complexEuclideanDiracBlock_isSelfAdjoint (mass j) (scale j)))
      ((x : ComplexDiracBlockHilbert) j)
      ((y : ComplexDiracBlockHilbert) j)

/-- A vector supported on one complex block lies in the maximal domain. -/
theorem complexSingleBlock_mem_maximalComplexDiracDomain
    (mass scale : ℕ → ℝ) (j : ℕ)
    (v : EuclideanSpace ℂ (Fin 2)) :
    (lp.single 2 j v : ComplexDiracBlockHilbert) ∈
      maximalComplexDiracDomain mass scale := by
  have h := complexFiniteBlockTruncation_mem_maximalComplexDiracDomain
    mass scale (lp.single 2 j v) {j}
  simpa [complexFiniteBlockTruncation] using h

/-- D acts on a single-block vector by that block's matrix alone. -/
theorem maximalComplexDiracPMap_singleBlock_apply
    (mass scale : ℕ → ℝ) (j : ℕ)
    (v : EuclideanSpace ℂ (Fin 2)) :
    (maximalComplexDiracPMap mass scale)
        ⟨lp.single 2 j v,
          complexSingleBlock_mem_maximalComplexDiracDomain mass scale j v⟩ =
      lp.single 2 j (complexEuclideanDiracBlock (mass j) (scale j) v) := by
  apply lp.ext
  funext k
  change complexEuclideanDiracBlock (mass k) (scale k)
      ((lp.single 2 j v : ComplexDiracBlockHilbert) k) =
    (lp.single 2 j
      (complexEuclideanDiracBlock (mass j) (scale j) v) :
        ComplexDiracBlockHilbert) k
  by_cases hkj : k = j
  · subst k
    simp
  · simp [lp.single_apply, hkj]

/-- The complex Hilbert adjoint necessarily has the original
blockwise Dirac action at every coordinate. -/
theorem maximalComplexDiracPMap_adjoint_apply_coord
    (mass scale : ℕ → ℝ)
    (y : ComplexDiracBlockHilbert)
    (hy : y ∈ (maximalComplexDiracPMap mass scale).adjoint.domain)
    (j : ℕ) :
    ((maximalComplexDiracPMap mass scale).adjoint ⟨y, hy⟩) j =
      complexEuclideanDiracBlock (mass j) (scale j) (y j) := by
  apply ext_inner_right ℂ
  intro v
  have h := ((maximalComplexDiracPMap mass scale).adjoint_isFormalAdjoint
    (maximalComplexDiracDomain_dense mass scale))
      ⟨y, hy⟩
      ⟨lp.single 2 j v,
        complexSingleBlock_mem_maximalComplexDiracDomain mass scale j v⟩
  rw [lp.inner_single_right] at h
  rw [maximalComplexDiracPMap_singleBlock_apply] at h
  rw [lp.inner_single_right] at h
  calc
    inner ℂ (((maximalComplexDiracPMap mass scale).adjoint ⟨y, hy⟩) j) v =
        inner ℂ (y j) (complexEuclideanDiracBlock (mass j) (scale j) v) := h
    _ = inner ℂ
        (complexEuclideanDiracBlock (mass j) (scale j) (y j)) v :=
      ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (complexEuclideanDiracBlock_isSelfAdjoint (mass j) (scale j))) (y j) v).symm

/-- Adjoint-domain vectors satisfy the maximal square-summable image condition. -/
theorem maximalComplexDiracPMap_adjoint_domain_le
    (mass scale : ℕ → ℝ) :
    (maximalComplexDiracPMap mass scale).adjoint.domain ≤
      maximalComplexDiracDomain mass scale := by
  intro y hy
  change Memℓp (complexDiracBlockwise mass scale y) 2
  have heq : complexDiracBlockwise mass scale y =
      (((maximalComplexDiracPMap mass scale).adjoint ⟨y, hy⟩) :
        ℕ → EuclideanSpace ℂ (Fin 2)) := by
    funext j
    exact (maximalComplexDiracPMap_adjoint_apply_coord mass scale y hy j).symm
  rw [heq]
  exact lp.memℓp _

/-- The infinite complex direct sum of Hermitian two-point Dirac blocks
is self-adjoint on its maximal ℓ²-domain, for arbitrary real mass
and coupling sequences. -/
theorem maximalComplexDiracPMap_isSelfAdjoint
    (mass scale : ℕ → ℝ) :
    IsSelfAdjoint (maximalComplexDiracPMap mass scale) := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hle : maximalComplexDiracPMap mass scale ≤
      (maximalComplexDiracPMap mass scale).adjoint :=
    (maximalComplexDiracPMap_formalSymmetric mass scale).le_adjoint
      (maximalComplexDiracDomain_dense mass scale)
  have hdom : (maximalComplexDiracPMap mass scale).domain =
      (maximalComplexDiracPMap mass scale).adjoint.domain :=
    le_antisymm hle.1 (maximalComplexDiracPMap_adjoint_domain_le mass scale)
  exact (LinearPMap.eq_of_le_of_domain_eq hle hdom).symm

end Neoplatonic.LTR
