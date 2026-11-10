import Neoplatonic.LTR.TwoDirectionResidualCompression
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# LTR-MAN-61: two-dimensional trace-zero Hermitian residual normal form

MAN-60 compresses the signed coordinate operators to the invariant
residual submodule; in six ambient Hilbert dimensions this residual
has dimension two.

Every Hermitian trace-zero 2x2 complex matrix has the Pauli form

  H = [[a, z], [star z, -a]],  star a = a.

Its square is scalar and the anticommutator of any two such matrices
is likewise scalar. These are exact algebraic equations that turn
the remaining six-dimensional residual spectral constraints into a
small polynomial system.

This module proves the 2x2 matrix statements without assuming
a residual trace condition for the original Hilbert operators.
Transport of the ambient commutator trace into the residual subspace
and selection of an orthonormal residual basis are separate steps.
-/

namespace Neoplatonic.LTR

private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- A complex 2x2 trace-zero matrix in Pauli coordinates.
It is Hermitian when its diagonal parameter is self-adjoint. -/
noncomputable def pauliResidualMatrix (a z : ℂ) : TwoMat :=
  fun i j => if i = 0 then (if j = 0 then a else z)
    else if j = 0 then star z else -a

/-- Pauli coordinates are manifestly trace zero. -/
theorem pauliResidualMatrix_trace_zero (a z : ℂ) :
    (pauliResidualMatrix a z).trace = 0 := by
  change (∑ i : Fin 2, pauliResidualMatrix a z i i) = 0
  simp [Fin.sum_univ_two, pauliResidualMatrix]

/-- A real diagonal parameter makes this Pauli matrix Hermitian. -/
theorem pauliResidualMatrix_isHermitian (a z : ℂ)
    (ha : star a = a) :
    (pauliResidualMatrix a z).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliResidualMatrix, ha]

/-- Exact scalar-square identity, including arbitrary complex
off-diagonal phases. -/
theorem pauliResidualMatrix_square_scalar (a z : ℂ) :
    pauliResidualMatrix a z * pauliResidualMatrix a z =
      Matrix.diagonal (fun _ : Fin 2 => a ^ 2 + z * star z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliResidualMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.diagonal_apply] <;> ring

/-- The symmetrized product of two Pauli-form matrices is
scalar, even for complex off-diagonal entries. -/
theorem pauliResidualMatrix_anticommutator_scalar
    (a b z w : ℂ) :
    pauliResidualMatrix a z * pauliResidualMatrix b w +
      pauliResidualMatrix b w * pauliResidualMatrix a z =
      Matrix.diagonal (fun _ : Fin 2 =>
        2 * a * b + z * star w + w * star z) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliResidualMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.diagonal_apply] <;> ring

/-- Every traceless Hermitian complex 2x2 matrix is exactly
one Pauli-form matrix in its given orthonormal coordinates. -/
theorem twoDim_tracelessHermitian_pauli_normal_form
    (M : TwoMat) (hM : M.IsHermitian) (htr : M.trace = 0) :
    M = pauliResidualMatrix (M 0 0) (M 0 1) := by
  have h10 : M 1 0 = star (M 0 1) :=
    (hM.apply 1 0).symm
  have htr' : M 0 0 + M 1 1 = 0 := by
    have h : (∑ i : Fin 2, M i i) = 0 := htr
    simpa only [Fin.sum_univ_two] using h
  have h11 : M 1 1 = -M 0 0 := by
    linear_combination htr'
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliResidualMatrix, h10, h11]

/-- Every trace-zero Hermitian complex 2x2 operator squares
to a scalar multiple of the identity matrix. -/
theorem twoDim_tracelessHermitian_square_scalar
    (M : TwoMat) (hM : M.IsHermitian) (htr : M.trace = 0) :
    M * M =
      Matrix.diagonal (fun _ : Fin 2 =>
        (M 0 0) ^ 2 + (M 0 1) * star (M 0 1)) := by
  rw [twoDim_tracelessHermitian_pauli_normal_form M hM htr]
  exact pauliResidualMatrix_square_scalar (M 0 0) (M 0 1)

/-- The anticommutator of any pair of trace-zero Hermitian
2x2 matrices is scalar. This is the Pauli residual algebra. -/
theorem twoDim_tracelessHermitian_anticommutator_scalar
    (M N : TwoMat)
    (hM : M.IsHermitian) (hN : N.IsHermitian)
    (htrM : M.trace = 0) (htrN : N.trace = 0) :
    M * N + N * M =
      Matrix.diagonal (fun _ : Fin 2 =>
        2 * (M 0 0) * (N 0 0) +
          (M 0 1) * star (N 0 1) +
          (N 0 1) * star (M 0 1)) := by
  rw [twoDim_tracelessHermitian_pauli_normal_form M hM htrM,
    twoDim_tracelessHermitian_pauli_normal_form N hN htrN]
  exact pauliResidualMatrix_anticommutator_scalar
    (M 0 0) (N 0 0) (M 0 1) (N 0 1)

end Neoplatonic.LTR
