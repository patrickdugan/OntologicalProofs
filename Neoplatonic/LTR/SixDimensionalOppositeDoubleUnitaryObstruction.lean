import Neoplatonic.LTR.SixDimensionalSignedOppositeGram
import Mathlib.Tactic

/-!
# LTR-MAN-98: exact first-row energy obstruction in a two-dimensional unitary

The MAN-97 complementary corner projections lead, in the opposite
double (2+2) truth-fibre chart, to a two-by-two neutral exchange
matrix U. The remaining bridge must show that U is unitary in
the appropriate corner/neutral bases and that the original two
coordinate-commutator norms are the maximum of 1/2 and one
off-diagonal or diagonal modulus of U respectively.

This file supplies the independent exact algebraic obstruction:
a unitary U cannot have both a diagonal and an off-diagonal
entry in the same row of squared modulus greater than 1/2.
In particular they cannot both attain squared modulus one.

No conclusion about the original Dirac metric is claimed here
until the chart and norm identifications are kernel-verified.
-/

namespace Neoplatonic.LTR

private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- One row of a genuine complex 2x2 unitary is normalized
in the real sum of squared entry magnitudes. -/
theorem twoMatrix_unitary_firstRow_energy
    (U : TwoMat)
    (hU : U * U.conjTranspose = 1) :
    ‖U 0 0‖ ^ 2 + ‖U 0 1‖ ^ 2 = (1 : ℝ) := by
  have he := congrArg (fun M : TwoMat => M 0 0) hU
  have hRow :
      U 0 0 * star (U 0 0) +
        U 0 1 * star (U 0 1) = (1 : ℂ) := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, Matrix.one_apply] using he
  apply Complex.ofReal_injective
  have hCast :
      (((‖U 0 0‖ ^ 2 + ‖U 0 1‖ ^ 2 : ℝ) : ℂ)) = 1 := by
    rw [Complex.ofReal_add,
      complex_cast_norm_sq_eq_mul_star,
      complex_cast_norm_sq_eq_mul_star]
    exact hRow
  simpa using hCast

/-- At least one of the first-row entries has squared
complex magnitude at most one half. -/
theorem twoMatrix_unitary_firstRow_halfDichotomy
    (U : TwoMat)
    (hU : U * U.conjTranspose = 1) :
    ‖U 0 0‖ ^ 2 ≤ (1 / 2 : ℝ) ∨
      ‖U 0 1‖ ^ 2 ≤ (1 / 2 : ℝ) := by
  have hrow := twoMatrix_unitary_firstRow_energy U hU
  by_contra h
  push_neg at h
  rcases h with ⟨h0, h1⟩
  linarith

/-- An exact obstruction to simultaneously saturating two
orthogonal first-row unitary amplitudes. -/
theorem twoMatrix_unitary_firstRow_cannotBothUnit
    (U : TwoMat)
    (hU : U * U.conjTranspose = 1)
    (h00 : ‖U 0 0‖ = (1 : ℝ))
    (h01 : ‖U 0 1‖ = (1 : ℝ)) :
    False := by
  have hrow := twoMatrix_unitary_firstRow_energy U hU
  rw [h00, h01] at hrow
  norm_num at hrow

end Neoplatonic.LTR
