import Neoplatonic.LTR.FiveFibreConnesDualObstruction
import Neoplatonic.LTR.IdempotentGradingPairing
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

/-!
# LTR-MAN-36: literal Dirac coordinate spectral certificates

The two Boolean truth projections are diagonal matrices with entries
0 or 1, hence self-adjoint idempotents. For any Hermitian complex Dirac
matrix D, their imaginary commutators A=i[D,P], B=i[D,Q] are
self-adjoint and traceless.

The canonical gradings 2P-I and 2Q-I square to the identity and
anticommute with their respective imaginary commutators.
These matrix facts are the concrete hypotheses needed to apply
MAN-21's five-dimensional zero-product theorem to the actual Dirac
operators, after transport through the Euclidean Hilbert matrix map.
-/

namespace Neoplatonic.LTR

/-- The two Boolean coordinate projections as actual diagonal matrices. -/
def fiveFibreSquarePMatrix : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal fiveFibreSquareP

def fiveFibreSquareQMatrix : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.diagonal fiveFibreSquareQ

/-- The coordinate projections are idempotent as matrices. -/
theorem fiveFibreSquarePMatrix_idempotent :
    fiveFibreSquarePMatrix * fiveFibreSquarePMatrix =
      fiveFibreSquarePMatrix := by
  change Matrix.diagonal fiveFibreSquareP *
      Matrix.diagonal fiveFibreSquareP =
    Matrix.diagonal fiveFibreSquareP
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> norm_num [fiveFibreSquareP]

theorem fiveFibreSquareQMatrix_idempotent :
    fiveFibreSquareQMatrix * fiveFibreSquareQMatrix =
      fiveFibreSquareQMatrix := by
  change Matrix.diagonal fiveFibreSquareQ *
      Matrix.diagonal fiveFibreSquareQ =
    Matrix.diagonal fiveFibreSquareQ
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> norm_num [fiveFibreSquareQ]

/-- Their diagonal entries are real, so the projections are Hermitian. -/
theorem fiveFibreSquarePMatrix_selfAdjoint :
    IsSelfAdjoint fiveFibreSquarePMatrix := by
  apply Matrix.IsHermitian.isSelfAdjoint
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  fin_cases i <;> simp [fiveFibreSquarePMatrix, fiveFibreSquareP, IsSelfAdjoint]

theorem fiveFibreSquareQMatrix_selfAdjoint :
    IsSelfAdjoint fiveFibreSquareQMatrix := by
  apply Matrix.IsHermitian.isSelfAdjoint
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  fin_cases i <;> simp [fiveFibreSquareQMatrix, fiveFibreSquareQ, IsSelfAdjoint]

/-- Any Hermitian Dirac D has a Hermitian first-coordinate
imaginary commutator A=i[D,P]. -/
theorem fiveFibreSquareA_selfAdjoint
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hD : ∀ i j, D i j = star (D j i)) :
    IsSelfAdjoint (fiveFibreSquareA D) := by
  have hDSelf : IsSelfAdjoint D :=
    (Matrix.IsHermitian.ext fun i j => (hD i j).symm).isSelfAdjoint
  have hC : D * fiveFibreSquarePMatrix -
        fiveFibreSquarePMatrix * D ∈
      skewAdjoint (Matrix (Fin 5) (Fin 5) ℂ) := by
    rw [skewAdjoint.mem_iff]
    simp only [star_sub, star_mul, hDSelf.star_eq,
      fiveFibreSquarePMatrix_selfAdjoint.star_eq]
    abel
  rw [fiveFibreSquareA_eq_diagonal_commutator]
  exact Complex.isSelfAdjoint_I_smul_iff_mem_skewAdjoint.mpr hC

theorem fiveFibreSquareB_selfAdjoint
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hD : ∀ i j, D i j = star (D j i)) :
    IsSelfAdjoint (fiveFibreSquareB D) := by
  have hDSelf : IsSelfAdjoint D :=
    (Matrix.IsHermitian.ext fun i j => (hD i j).symm).isSelfAdjoint
  have hC : D * fiveFibreSquareQMatrix -
        fiveFibreSquareQMatrix * D ∈
      skewAdjoint (Matrix (Fin 5) (Fin 5) ℂ) := by
    rw [skewAdjoint.mem_iff]
    simp only [star_sub, star_mul, hDSelf.star_eq,
      fiveFibreSquareQMatrix_selfAdjoint.star_eq]
    abel
  rw [fiveFibreSquareB_eq_diagonal_commutator]
  exact Complex.isSelfAdjoint_I_smul_iff_mem_skewAdjoint.mpr hC

/-- The trace of either coordinate commutator vanishes because
every diagonal matrix entry is zero. -/
theorem fiveFibreSquareA_trace_zero
    (D : Matrix (Fin 5) (Fin 5) ℂ) :
    (fiveFibreSquareA D).trace = 0 := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_five,
    fiveFibreSquareA, fiveFibreSquareP]

theorem fiveFibreSquareB_trace_zero
    (D : Matrix (Fin 5) (Fin 5) ℂ) :
    (fiveFibreSquareB D).trace = 0 := by
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_five,
    fiveFibreSquareB, fiveFibreSquareQ]

/-- The two canonical involutive coordinate gradings. -/
def fiveFibreSquareGradeP : Matrix (Fin 5) (Fin 5) ℂ :=
  2 * fiveFibreSquarePMatrix - 1

def fiveFibreSquareGradeQ : Matrix (Fin 5) (Fin 5) ℂ :=
  2 * fiveFibreSquareQMatrix - 1

theorem fiveFibreSquareGradeP_square_one :
    fiveFibreSquareGradeP * fiveFibreSquareGradeP = 1 :=
  idempotent_grading_square_one
    fiveFibreSquarePMatrix fiveFibreSquarePMatrix_idempotent

theorem fiveFibreSquareGradeQ_square_one :
    fiveFibreSquareGradeQ * fiveFibreSquareGradeQ = 1 :=
  idempotent_grading_square_one
    fiveFibreSquareQMatrix fiveFibreSquareQMatrix_idempotent

/-- The first grading anticommutes with the first imaginary
Dirac coordinate commutator. -/
theorem fiveFibreSquareGradeP_anticommutes
    (D : Matrix (Fin 5) (Fin 5) ℂ) :
    fiveFibreSquareGradeP * fiveFibreSquareA D =
      -(fiveFibreSquareA D * fiveFibreSquareGradeP) := by
  let P := fiveFibreSquarePMatrix
  let C := D * P - P * D
  let G := 2 * P - 1
  have hp : P * P = P := fiveFibreSquarePMatrix_idempotent
  have hcomm : G * C = -(C * G) :=
    idempotent_grading_commutator_anticommutes D P hp
  have hA : fiveFibreSquareA D = Complex.I • C := by
    simpa [P, C, fiveFibreSquarePMatrix] using
      fiveFibreSquareA_eq_diagonal_commutator D
  change G * fiveFibreSquareA D = -(fiveFibreSquareA D * G)
  rw [hA]
  calc
    G * (Complex.I • C) = Complex.I • (G * C) := by
      rw [mul_smul_comm]
    _ = Complex.I • (-(C * G)) := by rw [hcomm]
    _ = -((Complex.I • C) * G) := by
      simp only [smul_neg, smul_mul_assoc]

theorem fiveFibreSquareGradeQ_anticommutes
    (D : Matrix (Fin 5) (Fin 5) ℂ) :
    fiveFibreSquareGradeQ * fiveFibreSquareB D =
      -(fiveFibreSquareB D * fiveFibreSquareGradeQ) := by
  let P := fiveFibreSquareQMatrix
  let C := D * P - P * D
  let G := 2 * P - 1
  have hp : P * P = P := fiveFibreSquareQMatrix_idempotent
  have hcomm : G * C = -(C * G) :=
    idempotent_grading_commutator_anticommutes D P hp
  have hB : fiveFibreSquareB D = Complex.I • C := by
    simpa [P, C, fiveFibreSquareQMatrix] using
      fiveFibreSquareB_eq_diagonal_commutator D
  change G * fiveFibreSquareB D = -(fiveFibreSquareB D * G)
  rw [hB]
  calc
    G * (Complex.I • C) = Complex.I • (G * C) := by
      rw [mul_smul_comm]
    _ = Complex.I • (-(C * G)) := by rw [hcomm]
    _ = -((Complex.I • C) * G) := by
      simp only [smul_neg, smul_mul_assoc]

end Neoplatonic.LTR
