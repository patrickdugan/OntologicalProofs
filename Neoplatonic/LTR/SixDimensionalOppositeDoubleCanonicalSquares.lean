import Neoplatonic.LTR.SixDimensionalOppositeDoubleUnitaryObstruction
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-99: canonical opposite-double coordinate squares

This is a self-contained exact six-dimensional check of the canonical
2+2 form conjectured in MAN-98. Basis order is:

  p00, q00, n01, n10, p11, q11.

The positive signed witness has a saturated active p00/p11 edge
of unit modulus and a unitary neutral exchange U between
the q00/q11 rows and the n01/n10 columns.

After recovering A=(W+ + W-)/2 and B=(W+ - W-)/2,
each coordinate commutator consists of three pairwise
orthogonal Hermitian edges. Their squares are therefore diagonal.

The resulting identities form the finite-matrix algebraic
precondition for a rigorous operator-norm obstruction.
These definitions are canonical models; relating them to arbitrary
labelled six-dimensional Dirac matrices remains a further theorem.
-/

namespace Neoplatonic.LTR

private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Canonical first coordinate commutator of the opposite-double model. -/
def sixOppositeDoubleCanonicalA (U : TwoMat) : SixMat :=
  !![(0 : ℂ), 0, 0, 0, (1 / 2 : ℂ), 0;
     0, 0, 0, U 0 1, 0, 0;
     0, 0, 0, 0, 0, star (U 1 0);
     0, star (U 0 1), 0, 0, 0, 0;
     (1 / 2 : ℂ), 0, 0, 0, 0, 0;
     0, 0, U 1 0, 0, 0, 0]

/-- Canonical second coordinate commutator of the opposite-double model. -/
def sixOppositeDoubleCanonicalB (U : TwoMat) : SixMat :=
  !![(0 : ℂ), 0, 0, 0, (1 / 2 : ℂ), 0;
     0, 0, U 0 0, 0, 0, 0;
     0, star (U 0 0), 0, 0, 0, 0;
     0, 0, 0, 0, 0, star (U 1 1);
     (1 / 2 : ℂ), 0, 0, 0, 0, 0;
     0, 0, 0, U 1 1, 0, 0]

/-- The first coordinate square has only diagonal entries: the
saturated active edge contributes 1/4 twice, and each neutral
exchange contribution is a squared complex modulus twice. -/
theorem sixOppositeDoubleCanonicalA_square (U : TwoMat) :
    sixOppositeDoubleCanonicalA U * sixOppositeDoubleCanonicalA U =
      Matrix.diagonal ![(1 / 4 : ℂ),
        U 0 1 * star (U 0 1),
        U 1 0 * star (U 1 0),
        U 0 1 * star (U 0 1),
        (1 / 4 : ℂ),
        U 1 0 * star (U 1 0)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sixOppositeDoubleCanonicalA,
      Matrix.mul_apply, Fin.sum_univ_six,
      Matrix.diagonal_apply] <;> ring

/-- The second coordinate square has the complementary diagonal
neutral-exchange entries and the same saturated active edge. -/
theorem sixOppositeDoubleCanonicalB_square (U : TwoMat) :
    sixOppositeDoubleCanonicalB U * sixOppositeDoubleCanonicalB U =
      Matrix.diagonal ![(1 / 4 : ℂ),
        U 0 0 * star (U 0 0),
        U 0 0 * star (U 0 0),
        U 1 1 * star (U 1 1),
        (1 / 4 : ℂ),
        U 1 1 * star (U 1 1)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sixOppositeDoubleCanonicalB,
      Matrix.mul_apply, Fin.sum_univ_six,
      Matrix.diagonal_apply] <;> ring

/-- The canonical coordinate commutator A is Hermitian. -/
theorem sixOppositeDoubleCanonicalA_hermitian (U : TwoMat) :
    (sixOppositeDoubleCanonicalA U).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sixOppositeDoubleCanonicalA, Matrix.conjTranspose_apply] <;> norm_num

/-- The canonical coordinate commutator B is Hermitian. -/
theorem sixOppositeDoubleCanonicalB_hermitian (U : TwoMat) :
    (sixOppositeDoubleCanonicalB U).IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sixOppositeDoubleCanonicalB, Matrix.conjTranspose_apply] <;> norm_num

end Neoplatonic.LTR
