import Neoplatonic.LTR.EuclideanDiracAdjoint
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Symmetry of the actual maximal-domain infinite Dirac operator

Each finite Dirac block is self-adjoint. The maximal-domain operator
applies those blocks coordinatewise on a real Hilbert direct sum.
The Hilbert inner product is the sum of the block inner products,
and their symmetry holds term by term.

This establishes that the unbounded LinearPMap is its own *formal*
adjoint on its domain. Self-adjointness further requires equality
with the maximal adjoint, including equality of domains.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- The maximal-domain infinite Dirac action is formally symmetric
as a genuine unbounded Hilbert-space partial linear map. -/
theorem maximalDiracPMap_formalSymmetric
    (mass scale : ℕ → ℝ) :
    (maximalDiracPMap mass scale).IsFormalAdjoint
      (maximalDiracPMap mass scale) := by
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  apply tsum_congr
  intro j
  change inner ℝ
      (euclideanDiracBlock (mass j) (scale j) ((x : DiracBlockHilbert) j))
      ((y : DiracBlockHilbert) j) =
    inner ℝ ((x : DiracBlockHilbert) j)
      (euclideanDiracBlock (mass j) (scale j) ((y : DiracBlockHilbert) j))
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (euclideanDiracBlock_isSelfAdjoint (mass j) (scale j)))
      ((x : DiracBlockHilbert) j) ((y : DiracBlockHilbert) j)

end Neoplatonic.LTR
