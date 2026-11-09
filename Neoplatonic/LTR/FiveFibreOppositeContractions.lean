import Neoplatonic.LTR.TwoBitOppositeWitnesses
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# LTR-MAN-28: the actual opposite-corner witnesses bound A+B and A-B

On the canonical five-dimensional faithful Boolean-square
representation, the observable (0,1,1,2) is p+q and
(1,0,2,1) is 1-p+q. At the duplicated coordinate 4 the
observable value equals its value at 0.

The corresponding complex Dirac commutators equal, up to
multiplication by i, the sums and differences of the coordinate
Hermitian commutators. Scalar multiplication by i preserves
the actual continuous-Hilbert-operator norm.

Therefore admissibility of the two forced opposite-corner witnesses
from MAN-27 yields both contraction bounds required by MAN-21.

The normalized opposite-distance witnesses and their attainment
remain separate premises.
-/

namespace Neoplatonic.LTR

/-- Pull back a four-vertex observable to the five Hilbert coordinates
with coordinate four duplicating the 00 truth fibre. -/
def fiveFibreSquareLift (f : Fin 4 → ℂ) (i : Fin 5) : ℂ :=
  if i = 0 then f 0 else if i = 1 then f 1
  else if i = 2 then f 2 else if i = 3 then f 3 else f 0

/-- The distance-to-00 observable is exactly the coordinate sum. -/
theorem fiveFibreSquareLift_sum_eq (i : Fin 5) :
    fiveFibreSquareLift twoBitOppositeCornerSum i =
      fiveFibreSquareP i + fiveFibreSquareQ i := by
  fin_cases i <;>
    norm_num [fiveFibreSquareLift, twoBitOppositeCornerSum,
      fiveFibreSquareP, fiveFibreSquareQ]

/-- The translated opposite-corner observable is 1-p+q. -/
theorem fiveFibreSquareLift_difference_eq (i : Fin 5) :
    fiveFibreSquareLift twoBitOppositeCornerDifference i =
      1 - fiveFibreSquareP i + fiveFibreSquareQ i := by
  fin_cases i <;>
    norm_num [fiveFibreSquareLift, twoBitOppositeCornerDifference,
      fiveFibreSquareP, fiveFibreSquareQ]

/-- The imaginary commutator of the distance-to-00 witness
equals the sum of the Hermitian coordinate commutators. -/
theorem fiveFibreSquare_sumWitness_matrix
    (D : Matrix (Fin 5) (Fin 5) ℂ) :
    fiveFibreSquareA D + fiveFibreSquareB D =
      Complex.I •
        (D * Matrix.diagonal
          (fiveFibreSquareLift twoBitOppositeCornerSum) -
         Matrix.diagonal
          (fiveFibreSquareLift twoBitOppositeCornerSum) * D) := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply,
    fiveFibreSquareA, fiveFibreSquareB,
    Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Pi.smul_apply, smul_eq_mul]
  rw [fiveFibreSquareLift_sum_eq, fiveFibreSquareLift_sum_eq]
  ring

/-- The imaginary commutator of the 01-to-10 witness
equals the second coordinate commutator minus the first. -/
theorem fiveFibreSquare_differenceWitness_matrix
    (D : Matrix (Fin 5) (Fin 5) ℂ) :
    fiveFibreSquareB D - fiveFibreSquareA D =
      Complex.I •
        (D * Matrix.diagonal
          (fiveFibreSquareLift twoBitOppositeCornerDifference) -
         Matrix.diagonal
          (fiveFibreSquareLift twoBitOppositeCornerDifference) * D) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply,
    fiveFibreSquareA, fiveFibreSquareB,
    Matrix.mul_diagonal, Matrix.diagonal_mul,
    Pi.smul_apply, smul_eq_mul]
  rw [fiveFibreSquareLift_difference_eq,
    fiveFibreSquareLift_difference_eq]
  ring

/-- Multiplication by the imaginary unit preserves the norm of
the continuous Hilbert-space operator associated to a complex matrix. -/
theorem fiveFibreSquare_imaginaryOperator_norm
    (M : Matrix (Fin 5) (Fin 5) ℂ) :
    ‖(Complex.I • M).toEuclideanLin.toContinuousLinearMap‖ =
      ‖M.toEuclideanLin.toContinuousLinearMap‖ := by
  have hs :
      (Complex.I • M).toEuclideanLin.toContinuousLinearMap =
        Complex.I • M.toEuclideanLin.toContinuousLinearMap := by
    ext v
    simp
  rw [hs, norm_smul]
  simp

/-- Two opposite-corner Dirac commutator unit witnesses
bound the genuine continuous Hilbert-space operators A+B and A-B. -/
theorem fiveFibreSquare_oppositeWitnesses_contractions
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hsum :
      ‖(D * Matrix.diagonal
          (fiveFibreSquareLift twoBitOppositeCornerSum) -
         Matrix.diagonal
          (fiveFibreSquareLift twoBitOppositeCornerSum) * D
        ).toEuclideanLin.toContinuousLinearMap‖ ≤ 1)
    (hdiff :
      ‖(D * Matrix.diagonal
          (fiveFibreSquareLift twoBitOppositeCornerDifference) -
         Matrix.diagonal
          (fiveFibreSquareLift twoBitOppositeCornerDifference) * D
        ).toEuclideanLin.toContinuousLinearMap‖ ≤ 1) :
    ‖(fiveFibreSquareA D + fiveFibreSquareB D
       ).toEuclideanLin.toContinuousLinearMap‖ ≤ 1 ∧
    ‖(fiveFibreSquareA D - fiveFibreSquareB D
       ).toEuclideanLin.toContinuousLinearMap‖ ≤ 1 := by
  constructor
  · rw [fiveFibreSquare_sumWitness_matrix,
      fiveFibreSquare_imaginaryOperator_norm]
    exact hsum
  · have hminus :
        ‖(fiveFibreSquareB D - fiveFibreSquareA D
          ).toEuclideanLin.toContinuousLinearMap‖ ≤ 1 := by
      rw [fiveFibreSquare_differenceWitness_matrix,
        fiveFibreSquare_imaginaryOperator_norm]
      exact hdiff
    have hneg :
        fiveFibreSquareA D - fiveFibreSquareB D =
          -(fiveFibreSquareB D - fiveFibreSquareA D) := by
      abel
    rw [hneg]
    have hnorm :
        ‖(-(fiveFibreSquareB D - fiveFibreSquareA D)
          ).toEuclideanLin.toContinuousLinearMap‖ =
          ‖(fiveFibreSquareB D - fiveFibreSquareA D
          ).toEuclideanLin.toContinuousLinearMap‖ := by
      have h :
          (-(fiveFibreSquareB D - fiveFibreSquareA D)
            ).toEuclideanLin.toContinuousLinearMap =
            -((fiveFibreSquareB D - fiveFibreSquareA D)
              ).toEuclideanLin.toContinuousLinearMap := by
        ext v
        simp
      rw [h, norm_neg]
    rw [hnorm]
    exact hminus

end Neoplatonic.LTR
