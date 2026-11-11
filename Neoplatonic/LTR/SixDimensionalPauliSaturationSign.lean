import Neoplatonic.LTR.SixDimensionalExactHammingResidualWitnessExtinction
import Mathlib.Tactic

/-!
# LTR-MAN-88: select the sign of a saturated residual Pauli pair

MAN-87 proves that at maximal residual mixed overlap the two
traceless Hermitian 2x2 Pauli matrices coincide up to a sign.
The actual signed coefficient distinguishes these two options.

The mixed coefficient of a Hermitian Pauli matrix with itself is
twice its nonnegative real Pauli quadratic. Negating the first
argument negates the mixed coefficient.

At q_M=q_N=1/4, the positive overlap c=+1/2 therefore forces
M=N, while the negative overlap c=-1/2 forces M=-N.
All identities concern actual matrix equality, in the same
orthonormal residual basis, not a change-of-basis gauge choice.
-/

namespace Neoplatonic.LTR

private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- The real Pauli mixed coefficient is linear under negation of
its first matrix, with all complex phases preserved. -/
theorem pauliRealMixed_neg_left (M N : TwoMat) :
    pauliRealMixed (-M) N = -pauliRealMixed M N := by
  simp [pauliRealMixed, pauliMixed, Matrix.neg_apply, star_neg]
  ring

/-- Hermitian Pauli self-overlap is twice its squared real
three-vector length. -/
theorem pauliRealMixed_self_eq_twoQuadratic
    (M : TwoMat) (hM : M.IsHermitian) :
    pauliRealMixed M M = 2 * pauliRealQuadratic M := by
  rw [pauliRealMixed_eq_two_dot M M hM hM,
    pauliRealQuadratic_eq_dot M hM]

/-- Positive extremal overlap selects equality of the original
two Hermitian Pauli matrices in their common residual basis. -/
theorem twoDim_pauli_halfSat_positive_select_equal
    (M N : TwoMat) (hM : M.IsHermitian) (hN : N.IsHermitian)
    (htrM : M.trace = 0) (htrN : N.trace = 0)
    (hq : pauliRealQuadratic M = (1 / 4 : ℝ))
    (hr : pauliRealQuadratic N = (1 / 4 : ℝ))
    (hc : pauliRealMixed M N = (1 / 2 : ℝ)) :
    M = N := by
  have hsat : |pauliRealMixed M N| = (1 / 2 : ℝ) := by
    rw [hc]
    norm_num
  rcases twoDim_pauli_halfSat_matrices_equal_or_negative
    M N hM hN htrM htrN hq hr hsat with heq | hneg
  · exact heq
  · have hwrong := hc
    rw [hneg, pauliRealMixed_neg_left,
      pauliRealMixed_self_eq_twoQuadratic N hN, hr] at hwrong
    norm_num at hwrong

/-- Negative extremal overlap selects negation of the original
two Hermitian Pauli matrices. -/
theorem twoDim_pauli_halfSat_negative_select_opposite
    (M N : TwoMat) (hM : M.IsHermitian) (hN : N.IsHermitian)
    (htrM : M.trace = 0) (htrN : N.trace = 0)
    (hq : pauliRealQuadratic M = (1 / 4 : ℝ))
    (hr : pauliRealQuadratic N = (1 / 4 : ℝ))
    (hc : pauliRealMixed M N = -(1 / 2 : ℝ)) :
    M = -N := by
  have hsat : |pauliRealMixed M N| = (1 / 2 : ℝ) := by
    rw [hc]
    norm_num
  rcases twoDim_pauli_halfSat_matrices_equal_or_negative
    M N hM hN htrM htrN hq hr hsat with heq | hneg
  · have hwrong := hc
    rw [heq, pauliRealMixed_self_eq_twoQuadratic N hN, hr] at hwrong
    norm_num at hwrong
  · exact hneg

end Neoplatonic.LTR
