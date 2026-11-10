import Neoplatonic.LTR.SixDimensionalResidualQuadratics
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-67: exact C*-operator norm of a Pauli quadratic

MAN-66 proves scalar-square identities for the two genuine
compressed Hamming operators in the 6D residual sector.
The relevant norm on complex square matrices is the
L2-induced Hilbert operator norm, not an entrywise norm.

For traceless Hermitian two-by-two matrices the scalar-square
identities together with the C*-identity give exact squared-norm
equations. The contractions of a pair of matrices imply
explicit modulus bounds for the plus/minus Pauli coefficients.

The final transport from the ambient residual CLM contractions
to the concrete matrices from MAN-65 uses unitary covariance
of the matrix representation and remains a separate lemma.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- In the actual C*-operator matrix norm, the squared norm of
a traceless Hermitian two-by-two matrix equals the modulus of
its scalar Pauli quadratic coefficient. -/
theorem twoDim_pauli_operator_norm_sq
    (M : TwoMat) (hM : M.IsHermitian) (htr : M.trace = 0) :
    ‖pauliQuadratic M‖ = ‖M‖ ^ 2 := by
  have hCstar := Matrix.l2_opNorm_conjTranspose_mul_self M
  rw [hM.eq] at hCstar
  rw [twoDim_pauli_square M hM htr,
    Matrix.l2_opNorm_diagonal, pi_norm_const] at hCstar
  simpa only [pow_two] using hCstar

/-- The squared C*-norm of a Pauli sum equals the modulus of
its explicitly computed quadratic scalar. -/
theorem twoDim_pauli_sum_operator_norm_sq
    (M N : TwoMat)
    (hM : M.IsHermitian) (hN : N.IsHermitian)
    (htrM : M.trace = 0) (htrN : N.trace = 0) :
    ‖pauliQuadratic M + pauliQuadratic N + pauliMixed M N‖ =
      ‖M + N‖ ^ 2 := by
  have hsumSelf : Matrix.conjTranspose (M + N) = M + N := by
    simp only [Matrix.conjTranspose_add, hM.eq, hN.eq]
  have hCstar := Matrix.l2_opNorm_conjTranspose_mul_self (M + N)
  rw [hsumSelf] at hCstar
  rw [twoDim_pauli_add_square M N hM hN htrM htrN,
    Matrix.l2_opNorm_diagonal, pi_norm_const] at hCstar
  simpa only [pow_two] using hCstar

/-- The corresponding squared C*-operator norm of a
Pauli difference has its mixed coefficient subtracted. -/
theorem twoDim_pauli_difference_operator_norm_sq
    (M N : TwoMat)
    (hM : M.IsHermitian) (hN : N.IsHermitian)
    (htrM : M.trace = 0) (htrN : N.trace = 0) :
    ‖pauliQuadratic M + pauliQuadratic N - pauliMixed M N‖ =
      ‖M - N‖ ^ 2 := by
  have hsubSelf : Matrix.conjTranspose (M - N) = M - N := by
    simp only [Matrix.conjTranspose_sub, hM.eq, hN.eq]
  have hCstar := Matrix.l2_opNorm_conjTranspose_mul_self (M - N)
  rw [hsubSelf] at hCstar
  rw [twoDim_pauli_sub_square M N hM hN htrM htrN,
    Matrix.l2_opNorm_diagonal, pi_norm_const] at hCstar
  simpa only [pow_two] using hCstar

/-- Two C*-operator contractions in sum and difference constrain
the plus/minus scalar coefficients of the Pauli residual. -/
theorem twoDim_pauli_simultaneous_contraction_coefficients
    (M N : TwoMat)
    (hM : M.IsHermitian) (hN : N.IsHermitian)
    (htrM : M.trace = 0) (htrN : N.trace = 0)
    (hplus : ‖M + N‖ ≤ 1)
    (hminus : ‖M - N‖ ≤ 1) :
    ‖pauliQuadratic M + pauliQuadratic N + pauliMixed M N‖ ≤ 1 ∧
    ‖pauliQuadratic M + pauliQuadratic N - pauliMixed M N‖ ≤ 1 := by
  have hp :
      ‖M + N‖ ^ 2 ≤ (1 : ℝ) := by
    have h := (sq_le_sq₀ (norm_nonneg (M + N)) (by norm_num : (0 : ℝ) ≤ 1)).mpr hplus
    simpa using h
  have hm :
      ‖M - N‖ ^ 2 ≤ (1 : ℝ) := by
    have h := (sq_le_sq₀ (norm_nonneg (M - N)) (by norm_num : (0 : ℝ) ≤ 1)).mpr hminus
    simpa using h
  constructor
  · rw [twoDim_pauli_sum_operator_norm_sq M N hM hN htrM htrN]
    exact hp
  · rw [twoDim_pauli_difference_operator_norm_sq M N hM hN htrM htrN]
    exact hm

end Neoplatonic.LTR
