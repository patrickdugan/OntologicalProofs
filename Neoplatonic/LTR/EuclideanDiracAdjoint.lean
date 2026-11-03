import Neoplatonic.LTR.UnboundedDiracClosed
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Self-adjointness of every finite-dimensional Dirac block

The two-point real Dirac matrix is Hermitian, and the corresponding
continuous linear endomorphism of EuclideanSpace ℝ (Fin 2) is therefore
self-adjoint. This is the pointwise symmetry input for the formal
adjoint calculation of the infinite maximal-domain operator.

This theorem applies to each individual finite block; global
self-adjointness of the infinite direct sum still requires its own
adjoint-domain argument.
-/

namespace Neoplatonic.LTR

/-- The real symmetric 2-by-2 mass-shifted Dirac matrix is Hermitian. -/
theorem massDirac_isHermitian (mass scale : ℝ) :
    (massDirac mass scale).IsHermitian := by
  change (massDirac mass scale)ᴴ = massDirac mass scale
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [massDirac, Matrix.conjTranspose_apply] <;> ring

/-- The induced Euclidean operator is self-adjoint in the Hilbert sense. -/
theorem euclideanDiracBlock_isSelfAdjoint (mass scale : ℝ) :
    IsSelfAdjoint (euclideanDiracBlock mass scale) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  have h : ((massDirac mass scale).toEuclideanLin).IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (massDirac_isHermitian mass scale)
  simpa only [euclideanDiracBlock, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
    using h

end Neoplatonic.LTR
