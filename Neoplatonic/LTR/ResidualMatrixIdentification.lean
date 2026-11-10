import Neoplatonic.LTR.TwoDimensionalCstarMatrixTransport
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# LTR-MAN-70: identify the two six-dimensional residual matrix constructions

MAN-65 represents the actual compressed coordinate operators in a
common orthonormal basis, using toMatrixOrthonormal.

MAN-69 transports those same compressed operators into standard
two-dimensional Euclidean space through that orthonormal basis and
applies the inverse of the matrix-to-Euclidean continuous linear
operator equivalence.

These constructions give exactly the same complex 2x2 matrices.
The entries are inner products of the residual operator images with
the common orthonormal basis vectors. This is the analytic connection
between the Pauli normal form and the genuine operator contractions.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev TwoEuclidean := EuclideanSpace ℂ (Fin 2)
private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- The matrix of a standard Euclidean-space operator has entries
given by its inner products with the standard orthonormal basis. -/
theorem twoEuclideanCstarMatrix_apply_inner
    (T : TwoEuclidean →L[ℂ] TwoEuclidean) (i j : Fin 2) :
    twoEuclideanCstarMatrix T i j =
      inner ℂ (EuclideanSpace.basisFun (Fin 2) ℂ i)
        (T (EuclideanSpace.basisFun (Fin 2) ℂ j)) := by
  change (LinearMap.toMatrixOrthonormal
    (EuclideanSpace.basisFun (Fin 2) ℂ) T.toLinearMap) i j = _
  exact LinearMap.toMatrixOrthonormal_apply_apply
    (EuclideanSpace.basisFun (Fin 2) ℂ) T.toLinearMap i j

/-- A bounded operator represented through a genuine orthonormal
basis agrees with the C*-matrix representation of its isometric
conjugate on standard Euclidean space. -/
theorem twoEuclideanCstarMatrix_isometricConjugate
    {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]
    (b : OrthonormalBasis (Fin 2) ℂ H)
    (T : H →L[ℂ] H) :
    twoEuclideanCstarMatrix
        (hilbertIsometricConjugate b.repr T) =
      LinearMap.toMatrixOrthonormal b T.toLinearMap := by
  ext i j
  rw [twoEuclideanCstarMatrix_apply_inner,
    LinearMap.toMatrixOrthonormal_apply_apply]
  change inner ℂ (EuclideanSpace.basisFun (Fin 2) ℂ i)
    (b.repr (T (b.repr.symm
      (EuclideanSpace.basisFun (Fin 2) ℂ j)))) =
    inner ℂ (b i) (T (b j))
  simp only [EuclideanSpace.basisFun_apply,
    OrthonormalBasis.repr_symm_single]
  rw [← OrthonormalBasis.repr_self b i]
  exact b.repr.inner_map_map (b i) (T (b j))

section ActualSixDimensionalResidual

variable {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [CompleteSpace H]

/-- The actual compressed A matrix from MAN-65 is identical to
the C*-matrix transport of MAN-69, in the same residual basis. -/
theorem TwoDirectionExtremalSystem.sixDimCstarResidualMatrixA_eq
    (S : TwoDirectionExtremalSystem H)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ H = 6) :
    S.sixDimCstarResidualMatrixA hq hDim =
      S.sixDimResidualMatrixA hq hDim := by
  exact twoEuclideanCstarMatrix_isometricConjugate
    (S.sixDimResidualBasis hq hDim) S.residualA

/-- The analogous identification holds for B. -/
theorem TwoDirectionExtremalSystem.sixDimCstarResidualMatrixB_eq
    (S : TwoDirectionExtremalSystem H)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ H = 6) :
    S.sixDimCstarResidualMatrixB hq hDim =
      S.sixDimResidualMatrixB hq hDim := by
  exact twoEuclideanCstarMatrix_isometricConjugate
    (S.sixDimResidualBasis hq hDim) S.residualB

/-- In the common residual Pauli basis, the original ambient
Hamming contractions imply simultaneous genuine matrix C*-norm
contractions for the MAN-65 coordinate matrices. -/
theorem TwoDirectionExtremalSystem.sixDimResidualMatrix_contracts
    (S : TwoDirectionExtremalSystem H)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ H = 6) :
    ‖S.sixDimResidualMatrixA hq hDim +
       S.sixDimResidualMatrixB hq hDim‖ ≤ 1 ∧
    ‖S.sixDimResidualMatrixA hq hDim -
       S.sixDimResidualMatrixB hq hDim‖ ≤ 1 := by
  simpa only [S.sixDimCstarResidualMatrixA_eq hq hDim,
    S.sixDimCstarResidualMatrixB_eq hq hDim] using
      S.sixDimCstarResidual_contracts hq hDim

end ActualSixDimensionalResidual
end Neoplatonic.LTR
