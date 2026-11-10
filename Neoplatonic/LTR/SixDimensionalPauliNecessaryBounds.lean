import Neoplatonic.LTR.ResidualMatrixIdentification
import Neoplatonic.LTR.TwoDimensionalPauliOperatorNorm
import Mathlib.Tactic

/-!
# LTR-MAN-71: actual six-dimensional residual Pauli coefficient bounds

MAN-65 expresses the genuine six-dimensional residual coordinate
commutators as traceless Hermitian Pauli matrices in the same
orthonormal basis. MAN-70 identifies these matrices with the
isometric matrix transport of the original bounded operators,
proving their simultaneous C*-operator contraction bounds.

The exact C*-identity and scalar-square formulas in MAN-67 then
constrain the Pauli coefficients of the *actual* residual operators.

The resulting inequalities are algebraic necessary conditions for
a six-dimensional Hamming spectral representation. Whether these
inequalities admit a compatible four-atom truth representation is
the remaining geometric question.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The true two-dimensional residual matrices of a six-dimensional
graded Hamming coordinate system satisfy both Pauli scalar
contraction inequalities, with arbitrary complex off-diagonal phases. -/
theorem TwoDirectionExtremalSystem.sixDimResidual_pauliCoefficients_le_one
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ E = 6)
    (htrA : LinearMap.trace ℂ E S.A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ E S.B.toLinearMap = 0) :
    let M := S.sixDimResidualMatrixA hq hDim
    let N := S.sixDimResidualMatrixB hq hDim
    ‖pauliQuadratic M + pauliQuadratic N + pauliMixed M N‖ ≤ 1 ∧
      ‖pauliQuadratic M + pauliQuadratic N - pauliMixed M N‖ ≤ 1 := by
  dsimp
  exact twoDim_pauli_simultaneous_contraction_coefficients
    (S.sixDimResidualMatrixA hq hDim)
    (S.sixDimResidualMatrixB hq hDim)
    (S.sixDimResidualMatrixA_isHermitian hq hDim)
    (S.sixDimResidualMatrixB_isHermitian hq hDim)
    (S.sixDimResidualMatrixA_trace_zero hq hDim htrA)
    (S.sixDimResidualMatrixB_trace_zero hq hDim htrB)
    (S.sixDimResidualMatrix_contracts hq hDim).1
    (S.sixDimResidualMatrix_contracts hq hDim).2

/-- Equivalently the two exact squares computed in MAN-66 are
bounded in their scalar C*-norm coefficient by one. -/
theorem TwoDirectionExtremalSystem.sixDimResidual_quadraticBound
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ E = 6)
    (htrA : LinearMap.trace ℂ E S.A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ E S.B.toLinearMap = 0) :
    ∀ sign : Bool,
      let M := S.sixDimResidualMatrixA hq hDim
      let N := S.sixDimResidualMatrixB hq hDim
      ‖pauliQuadratic M + pauliQuadratic N +
        (if sign then pauliMixed M N else -pauliMixed M N)‖ ≤ 1 := by
  intro sign
  obtain ⟨hp, hm⟩ :=
    S.sixDimResidual_pauliCoefficients_le_one hq hDim htrA htrB
  cases sign with
  | false => simpa [add_neg_eq_sub] using hm
  | true => simpa using hp

end Neoplatonic.LTR
