import Neoplatonic.LTR.SixDimensionalOppositeBlockSignSelection
import Mathlib.Tactic

/-!
# LTR-MAN-89: exact involution of a twice-scaled Hermitian Pauli residual

The genuine six-dimensional signed extremal eigenquartet has a common
two-dimensional residual. MAN-65 identifies its coordinate operators
as Hermitian traceless 2×2 matrices, in one orthonormal basis.

For any such matrix M, the exact Pauli square formula gives
  M² = q_M I,
where q_M is the real Pauli length squared. Therefore, if q_M=1/4,
  (2M)² = I.
This is an exact identity of genuine complex matrices, including
arbitrary off-diagonal phases.

The statements here require no metric hypothesis beyond the inputs;
MAN-88 will specialize them to the surviving signed Hamming witness
for the same Hermitian Dirac matrix.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- The Pauli quadratic coefficient of a Hermitian 2×2 matrix is
exactly the complex embedding of its real quadratic coefficient. -/
theorem pauliQuadratic_eq_realQuadratic_of_hermitian
    (M : TwoMat) (hM : M.IsHermitian) :
    pauliQuadratic M = ((pauliRealQuadratic M : ℝ) : ℂ) := by
  have hdiag : (M 0 0).im = 0 :=
    pauliRealVector_diagonal_im_zero M hM
  apply Complex.ext
  · simp [pauliRealQuadratic]
  · simp [pauliQuadratic, pow_two, Complex.mul_im, Complex.star_def, hdiag]
    ring

/-- Twice a genuine Hermitian traceless Pauli matrix of
real quadratic coefficient one quarter is an exact involution
in the complex 2×2 C*-matrix algebra. -/
theorem twoDim_pauli_quarter_double_involution
    (M : TwoMat) (hM : M.IsHermitian)
    (htr : M.trace = 0)
    (hq : pauliRealQuadratic M = (1 / 4 : ℝ)) :
    ((2 : ℂ) • M) * ((2 : ℂ) • M) = 1 := by
  have hsq := twoDim_pauli_square M hM htr
  calc
    ((2 : ℂ) • M) * ((2 : ℂ) • M) =
        (4 : ℂ) • (M * M) := by
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      norm_num
    _ = (4 : ℂ) • Matrix.diagonal
          (fun _ : Fin 2 => pauliQuadratic M) := by rw [hsq]
    _ = 1 := by
      rw [pauliQuadratic_eq_realQuadratic_of_hermitian M hM, hq]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.smul_apply, Matrix.diagonal_apply,
          Matrix.one_apply, smul_eq_mul]

/-- The negative twice-scaled Pauli matrix has the same square,
so either sign yields an involution at quarter norm. -/
theorem twoDim_pauli_quarter_negDouble_involution
    (M : TwoMat) (hM : M.IsHermitian)
    (htr : M.trace = 0)
    (hq : pauliRealQuadratic M = (1 / 4 : ℝ)) :
    (-((2 : ℂ) • M)) * (-((2 : ℂ) • M)) = 1 := by
  simpa using twoDim_pauli_quarter_double_involution M hM htr hq

end Neoplatonic.LTR
