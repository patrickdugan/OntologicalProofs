import Neoplatonic.LTR.InfiniteDiracSymmetry
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Self-adjointness of the maximal infinite Dirac direct sum

The maximal-domain block operator is densely defined, closed and formally
symmetric. To prove equality with its Hilbert adjoint, test the adjoint on
vectors supported in one two-dimensional block. Each individual block is
self-adjoint. The adjoint vector therefore has block coordinates D_j y_j,
which are square summable because the adjoint vector lies in ℓ².

This proves domain equality, and hence self-adjointness, for arbitrary real
mass and scale sequences. The exponential mass growth is used separately
for compactness of the squared-resolvent candidate.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- A vector supported in one block belongs to the maximal Dirac domain. -/
theorem singleBlock_mem_maximalDiracDomain
    (mass scale : ℕ → ℝ) (j : ℕ)
    (v : EuclideanSpace ℝ (Fin 2)) :
    (lp.single 2 j v : DiracBlockHilbert) ∈
      maximalDiracDomain mass scale := by
  have h := finiteBlockTruncation_mem_maximalDiracDomain
    mass scale (lp.single 2 j v) {j}
  simpa [finiteBlockTruncation] using h

/-- The unbounded operator takes single-block vectors to single-block vectors. -/
theorem maximalDiracPMap_singleBlock_apply
    (mass scale : ℕ → ℝ) (j : ℕ)
    (v : EuclideanSpace ℝ (Fin 2)) :
    (maximalDiracPMap mass scale)
        ⟨lp.single 2 j v, singleBlock_mem_maximalDiracDomain mass scale j v⟩ =
      lp.single 2 j (euclideanDiracBlock (mass j) (scale j) v) := by
  apply lp.ext
  funext k
  change euclideanDiracBlock (mass k) (scale k)
      ((lp.single 2 j v : DiracBlockHilbert) k) =
    (lp.single 2 j (euclideanDiracBlock (mass j) (scale j) v) :
      DiracBlockHilbert) k
  by_cases hkj : k = j
  · subst k
    simp
  · simp [lp.single_apply, hkj]

/-- The adjoint of the maximal Dirac map agrees with the same block action
coordinatewise, whenever its input lies in the adjoint domain. -/
theorem maximalDiracPMap_adjoint_apply_coord
    (mass scale : ℕ → ℝ)
    (y : DiracBlockHilbert)
    (hy : y ∈ (maximalDiracPMap mass scale).adjoint.domain)
    (j : ℕ) :
    ((maximalDiracPMap mass scale).adjoint ⟨y, hy⟩) j =
      euclideanDiracBlock (mass j) (scale j) (y j) := by
  apply ext_inner_right ℝ
  intro v
  have h := ((maximalDiracPMap mass scale).adjoint_isFormalAdjoint
    (maximalDiracDomain_dense mass scale))
      ⟨y, hy⟩
      ⟨lp.single 2 j v, singleBlock_mem_maximalDiracDomain mass scale j v⟩
  rw [lp.inner_single_right] at h
  rw [maximalDiracPMap_singleBlock_apply] at h
  rw [lp.inner_single_right] at h
  calc
    inner ℝ (((maximalDiracPMap mass scale).adjoint ⟨y, hy⟩) j) v =
        inner ℝ (y j) (euclideanDiracBlock (mass j) (scale j) v) := h
    _ = inner ℝ (euclideanDiracBlock (mass j) (scale j) (y j)) v :=
      ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
        (euclideanDiracBlock_isSelfAdjoint (mass j) (scale j))) (y j) v).symm

/-- The Hilbert adjoint domain is contained in the maximal blockwise domain. -/
theorem maximalDiracPMap_adjoint_domain_le
    (mass scale : ℕ → ℝ) :
    (maximalDiracPMap mass scale).adjoint.domain ≤
      maximalDiracDomain mass scale := by
  intro y hy
  change Memℓp (diracBlockwise mass scale y) 2
  have heq : diracBlockwise mass scale y =
      (((maximalDiracPMap mass scale).adjoint ⟨y, hy⟩) :
        ℕ → EuclideanSpace ℝ (Fin 2)) := by
    funext j
    exact (maximalDiracPMap_adjoint_apply_coord mass scale y hy j).symm
  rw [heq]
  exact lp.memℓp _

/-- The closed, densely defined infinite direct sum of real symmetric
two-by-two Dirac blocks is self-adjoint on its maximal ℓ² domain. -/
theorem maximalDiracPMap_isSelfAdjoint
    (mass scale : ℕ → ℝ) :
    IsSelfAdjoint (maximalDiracPMap mass scale) := by
  rw [LinearPMap.isSelfAdjoint_def]
  have hle : maximalDiracPMap mass scale ≤
      (maximalDiracPMap mass scale).adjoint :=
    (maximalDiracPMap_formalSymmetric mass scale).le_adjoint
      (maximalDiracDomain_dense mass scale)
  have hdom : (maximalDiracPMap mass scale).domain =
      (maximalDiracPMap mass scale).adjoint.domain :=
    le_antisymm hle.1 (maximalDiracPMap_adjoint_domain_le mass scale)
  exact (LinearPMap.eq_of_le_of_domain_eq hle hdom).symm

end Neoplatonic.LTR
