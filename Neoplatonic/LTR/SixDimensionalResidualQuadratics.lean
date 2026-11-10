import Neoplatonic.LTR.SixDimensionalResidualPauli
import Mathlib.Tactic

/-!
# LTR-MAN-66: quadratic Pauli identities for the six-dimensional residual

MAN-65 constructs the *actual* Hermitian, trace-zero two-by-two
matrices of the compressed Hamming coordinate operators on the
two-dimensional invariant residual Hilbert subspace in dimension six.

Here their squared norms are encoded algebraically through the two
Pauli quadratic forms. The squares of their sum and difference are
scalar matrices, with explicit coefficients. Both computations use
the genuine common orthonormal basis and therefore retain the
complex off-diagonal phases.

An inequality for those scalar coefficients follows after transporting
the operator-norm contraction to this same basis. That analytic
norm step remains a separate obligation.
-/

namespace Neoplatonic.LTR

private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- The scalar coefficient in the square of a traceless Hermitian
two-by-two matrix. -/
noncomputable def pauliQuadratic (M : TwoMat) : ℂ :=
  (M 0 0) ^ 2 + (M 0 1) * star (M 0 1)

/-- The scalar coefficient of the anticommutator of traceless
Hermitian two-by-two matrices. -/
noncomputable def pauliMixed (M N : TwoMat) : ℂ :=
  2 * (M 0 0) * (N 0 0) +
    (M 0 1) * star (N 0 1) +
    (N 0 1) * star (M 0 1)

/-- Every Hermitian traceless two-by-two matrix squares to its
Pauli quadratic coefficient times the identity. -/
theorem twoDim_pauli_square (M : TwoMat)
    (hM : M.IsHermitian) (htrM : M.trace = 0) :
    M * M = Matrix.diagonal (fun _ : Fin 2 => pauliQuadratic M) := by
  exact twoDim_tracelessHermitian_square_scalar M hM htrM

/-- The mixed Pauli form is exactly the scalar anticommutator. -/
theorem twoDim_pauli_anticommutator (M N : TwoMat)
    (hM : M.IsHermitian) (hN : N.IsHermitian)
    (htrM : M.trace = 0) (htrN : N.trace = 0) :
    M * N + N * M =
      Matrix.diagonal (fun _ : Fin 2 => pauliMixed M N) := by
  exact twoDim_tracelessHermitian_anticommutator_scalar
    M N hM hN htrM htrN

/-- The square of the sum is scalar, with an explicit quadratic
coefficient including the mixed Pauli product. -/
theorem twoDim_pauli_add_square (M N : TwoMat)
    (hM : M.IsHermitian) (hN : N.IsHermitian)
    (htrM : M.trace = 0) (htrN : N.trace = 0) :
    (M + N) * (M + N) =
      Matrix.diagonal (fun _ : Fin 2 =>
        pauliQuadratic M + pauliQuadratic N + pauliMixed M N) := by
  calc
    (M + N) * (M + N) =
        M * M + N * N + (M * N + N * M) := by
      noncomm_ring
    _ = Matrix.diagonal (fun _ : Fin 2 => pauliQuadratic M) +
          Matrix.diagonal (fun _ : Fin 2 => pauliQuadratic N) +
          Matrix.diagonal (fun _ : Fin 2 => pauliMixed M N) := by
      rw [twoDim_pauli_square M hM htrM,
        twoDim_pauli_square N hN htrN,
        twoDim_pauli_anticommutator M N hM hN htrM htrN]
    _ = Matrix.diagonal (fun _ : Fin 2 =>
          pauliQuadratic M + pauliQuadratic N + pauliMixed M N) := by
      ext i j
      by_cases hij : i = j <;>
        simp [Matrix.diagonal_apply, hij]

/-- The square of the difference is scalar with the opposite
sign on the mixed Pauli form. -/
theorem twoDim_pauli_sub_square (M N : TwoMat)
    (hM : M.IsHermitian) (hN : N.IsHermitian)
    (htrM : M.trace = 0) (htrN : N.trace = 0) :
    (M - N) * (M - N) =
      Matrix.diagonal (fun _ : Fin 2 =>
        pauliQuadratic M + pauliQuadratic N - pauliMixed M N) := by
  calc
    (M - N) * (M - N) =
        M * M + N * N - (M * N + N * M) := by
      noncomm_ring
    _ = Matrix.diagonal (fun _ : Fin 2 => pauliQuadratic M) +
          Matrix.diagonal (fun _ : Fin 2 => pauliQuadratic N) -
          Matrix.diagonal (fun _ : Fin 2 => pauliMixed M N) := by
      rw [twoDim_pauli_square M hM htrM,
        twoDim_pauli_square N hN htrN,
        twoDim_pauli_anticommutator M N hM hN htrM htrN]
    _ = Matrix.diagonal (fun _ : Fin 2 =>
          pauliQuadratic M + pauliQuadratic N - pauliMixed M N) := by
      ext i j
      by_cases hij : i = j <;>
        simp [Matrix.diagonal_apply, hij]

section ActualResidual

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]

/-- The simultaneous signed-coordinate *sum*, compressed to the
actual two-dimensional residual Hilbert space, has scalar square. -/
theorem TwoDirectionExtremalSystem.sixDimResidual_sum_square
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ E = 6)
    (htrA : LinearMap.trace ℂ E S.A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ E S.B.toLinearMap = 0) :
    let MA := S.sixDimResidualMatrixA hq hDim
    let MB := S.sixDimResidualMatrixB hq hDim
    (MA + MB) * (MA + MB) =
      Matrix.diagonal (fun _ : Fin 2 =>
        pauliQuadratic MA + pauliQuadratic MB + pauliMixed MA MB) := by
  dsimp
  exact twoDim_pauli_add_square _ _
    (S.sixDimResidualMatrixA_isHermitian hq hDim)
    (S.sixDimResidualMatrixB_isHermitian hq hDim)
    (S.sixDimResidualMatrixA_trace_zero hq hDim htrA)
    (S.sixDimResidualMatrixB_trace_zero hq hDim htrB)

/-- The difference, likewise compressed to the actual residual
Hilbert space, has the corresponding scalar square. -/
theorem TwoDirectionExtremalSystem.sixDimResidual_difference_square
    (S : TwoDirectionExtremalSystem E)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hDim : Module.finrank ℂ E = 6)
    (htrA : LinearMap.trace ℂ E S.A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ E S.B.toLinearMap = 0) :
    let MA := S.sixDimResidualMatrixA hq hDim
    let MB := S.sixDimResidualMatrixB hq hDim
    (MA - MB) * (MA - MB) =
      Matrix.diagonal (fun _ : Fin 2 =>
        pauliQuadratic MA + pauliQuadratic MB - pauliMixed MA MB) := by
  dsimp
  exact twoDim_pauli_sub_square _ _
    (S.sixDimResidualMatrixA_isHermitian hq hDim)
    (S.sixDimResidualMatrixB_isHermitian hq hDim)
    (S.sixDimResidualMatrixA_trace_zero hq hDim htrA)
    (S.sixDimResidualMatrixB_trace_zero hq hDim htrB)

end ActualResidual

end Neoplatonic.LTR
