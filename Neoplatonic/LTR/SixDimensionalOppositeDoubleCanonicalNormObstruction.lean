import Neoplatonic.LTR.SixDimensionalOppositeDoubleCanonicalSquares
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-101: exact norm obstruction in the opposite-double canonical model

MAN-99 gives explicit six-dimensional Hermitian coordinate-commutator
matrices A(U) and B(U). Their squares are diagonal, with entries
1/4 and squared moduli of the neutral exchange U.

The C*-identity ||Mᴴ M|| = ||M||² and the exact Hilbert matrix
norm of a diagonal matrix show that each of A(U), B(U)
has norm less than one whenever its corresponding two neutral
amplitudes have squared modulus at most 1/2.

For an arbitrary U∈U(2), two row and column orthonormality equations
identify the paired squared moduli and MAN-98's half-energy
dichotomy forces one of the two coordinate operators strictly below
unit norm.

This establishes the *canonical* 2+2 norm obstruction. The transport
from a true labelled six-dimensional Dirac witness to this canonical
model remains separate.
-/

namespace Neoplatonic.LTR

open Matrix.Norms.L2Operator

private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A 2x2 unitary has its first column normalized as well
as its first row. -/
theorem twoMatrix_unitary_firstColumn_energy
    (U : TwoMat) (hU : U * U.conjTranspose = 1) :
    ‖U 0 0‖ ^ 2 + ‖U 1 0‖ ^ 2 = (1 : ℝ) := by
  have hU' : U.conjTranspose * U = 1 := mul_eq_one_comm.mp hU
  have he := congrArg (fun M : TwoMat => M 0 0) hU'
  have hc :
      U 0 0 * star (U 0 0) +
        U 1 0 * star (U 1 0) = (1 : ℂ) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.one_apply, mul_comm] using he
  apply Complex.ofReal_injective
  rw [Complex.ofReal_add,
    complex_cast_norm_sq_eq_mul_star,
    complex_cast_norm_sq_eq_mul_star]
  exact hc

/-- The second row of a unitary has squared Euclidean norm one. -/
theorem twoMatrix_unitary_secondRow_energy
    (U : TwoMat) (hU : U * U.conjTranspose = 1) :
    ‖U 1 0‖ ^ 2 + ‖U 1 1‖ ^ 2 = (1 : ℝ) := by
  have he := congrArg (fun M : TwoMat => M 1 1) hU
  have hc :
      U 1 0 * star (U 1 0) +
        U 1 1 * star (U 1 1) = (1 : ℂ) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.one_apply] using he
  apply Complex.ofReal_injective
  rw [Complex.ofReal_add,
    complex_cast_norm_sq_eq_mul_star,
    complex_cast_norm_sq_eq_mul_star]
  exact hc

/-- The two off-diagonal squared moduli of a complex 2x2 unitary
are equal, and so are its two diagonal squared moduli. -/
theorem twoMatrix_unitary_pairedModuli
    (U : TwoMat) (hU : U * U.conjTranspose = 1) :
    ‖U 0 1‖ ^ 2 = ‖U 1 0‖ ^ 2 ∧
      ‖U 0 0‖ ^ 2 = ‖U 1 1‖ ^ 2 := by
  have h0 := twoMatrix_unitary_firstRow_energy U hU
  have hc := twoMatrix_unitary_firstColumn_energy U hU
  have h1 := twoMatrix_unitary_secondRow_energy U hU
  constructor <;> linarith

/-- If both off-diagonal 2x2 amplitudes have squared magnitude
at most 1/2, the exact six-dimensional canonical A has
strictly subunit Euclidean operator norm. -/
theorem sixOppositeDoubleCanonicalA_norm_lt_one
    (U : TwoMat)
    (h01 : ‖U 0 1‖ ^ 2 ≤ (1 / 2 : ℝ))
    (h10 : ‖U 1 0‖ ^ 2 ≤ (1 / 2 : ℝ)) :
    ‖sixOppositeDoubleCanonicalA U‖ < 1 := by
  let M : SixMat := sixOppositeDoubleCanonicalA U
  let v : Fin 6 → ℂ :=
    ![(1 / 4 : ℂ),
      U 0 1 * star (U 0 1),
      U 1 0 * star (U 1 0),
      U 0 1 * star (U 0 1),
      (1 / 4 : ℂ),
      U 1 0 * star (U 1 0)]
  have hv : ‖v‖ ≤ (1 / 2 : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
    intro i
    fin_cases i <;> simp [v, norm_mul, norm_star] <;>
      nlinarith [h01, h10]
  have hsquare : M.conjTranspose * M = Matrix.diagonal v := by
    rw [(sixOppositeDoubleCanonicalA_hermitian U).eq]
    exact sixOppositeDoubleCanonicalA_square U
  have hnorm : ‖M‖ * ‖M‖ = ‖v‖ := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self M
    rw [hsquare, Matrix.l2_opNorm_diagonal] at h
    exact h.symm
  have hsq : ‖M‖ * ‖M‖ ≤ (1 / 2 : ℝ) := by
    rw [hnorm]
    exact hv
  have hn : 0 ≤ ‖M‖ := norm_nonneg M
  change ‖M‖ < 1
  nlinarith

/-- The complementary diagonal pair controls the exact operator
norm of the canonical B coordinate witness in the same way. -/
theorem sixOppositeDoubleCanonicalB_norm_lt_one
    (U : TwoMat)
    (h00 : ‖U 0 0‖ ^ 2 ≤ (1 / 2 : ℝ))
    (h11 : ‖U 1 1‖ ^ 2 ≤ (1 / 2 : ℝ)) :
    ‖sixOppositeDoubleCanonicalB U‖ < 1 := by
  let M : SixMat := sixOppositeDoubleCanonicalB U
  let v : Fin 6 → ℂ :=
    ![(1 / 4 : ℂ),
      U 0 0 * star (U 0 0),
      U 0 0 * star (U 0 0),
      U 1 1 * star (U 1 1),
      (1 / 4 : ℂ),
      U 1 1 * star (U 1 1)]
  have hv : ‖v‖ ≤ (1 / 2 : ℝ) := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)).mpr
    intro i
    fin_cases i <;> simp [v, norm_mul, norm_star] <;>
      nlinarith [h00, h11]
  have hsquare : M.conjTranspose * M = Matrix.diagonal v := by
    rw [(sixOppositeDoubleCanonicalB_hermitian U).eq]
    exact sixOppositeDoubleCanonicalB_square U
  have hnorm : ‖M‖ * ‖M‖ = ‖v‖ := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self M
    rw [hsquare, Matrix.l2_opNorm_diagonal] at h
    exact h.symm
  have hsq : ‖M‖ * ‖M‖ ≤ (1 / 2 : ℝ) := by
    rw [hnorm]
    exact hv
  have hn : 0 ≤ ‖M‖ := norm_nonneg M
  change ‖M‖ < 1
  nlinarith

/-- The MAN-98 row-energy dichotomy, together with the exact
six-coordinate Gram squares, makes one of the two canonical
coordinate commutators strictly subunit in operator norm. -/
theorem twoMatrix_unitary_canonicalSignedWitness_normObstruction
    (U : TwoMat) (hU : U * U.conjTranspose = 1) :
    ‖sixOppositeDoubleCanonicalA U‖ < 1 ∨
      ‖sixOppositeDoubleCanonicalB U‖ < 1 := by
  obtain ⟨hOff, hDiag⟩ := twoMatrix_unitary_pairedModuli U hU
  rcases twoMatrix_unitary_firstRow_halfDichotomy U hU with h00 | h01
  · right
    exact sixOppositeDoubleCanonicalB_norm_lt_one U h00
      (by rw [← hDiag]; exact h00)
  · left
    exact sixOppositeDoubleCanonicalA_norm_lt_one U h01
      (by rw [← hOff]; exact h01)

end Neoplatonic.LTR
