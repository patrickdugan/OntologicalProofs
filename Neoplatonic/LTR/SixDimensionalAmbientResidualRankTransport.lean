import Neoplatonic.LTR.SixDimensionalOverneutralResidualDefect
import Neoplatonic.LTR.SixDimensionalResidualDefectProjection
import Neoplatonic.LTR.SixDimensionalAmbientPauliDefectNorm
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-176: ambient residual projector transport and rank rigidity

MAN-175 established that any original complex six-dimensional
matrix W satisfying W²=I-tP, P²=P, and rank(W)≤4 must have t=1.

The signed spectral-quartet argument of MAN-144 gives the
same scalar projection defect in the Hilbert C*-operator model.
This module transports that orthogonal residual projection through
Mathlib's exact complex matrix-to-Euclidean-C*-isomorphism, preserving
multiplication, subtraction, scalar multiplication, and idempotence.

Consequently the actual 6×6 matrix rank bound excludes every
nonzero residual scalar square µ. This theorem is independent of
near-half Pauli overlap and applies to either Hamming signed witness.

The next specialization uses the true orthogonal residual of the
exact-Hamming extremal quartet, the minus-witness rank≤4 from MAN-174,
and the Pauli scalar-square identity to force µminus=0.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A projection in the actual six-dimensional Hilbert operator
algebra becomes an idempotent matrix in the original coordinate
basis under the exact C*-isomorphism. -/
theorem sixMatrix_residualProjection_transport_idempotent
    (P : SixH →L[ℂ] SixH)
    (hP : P * P = P) :
    let F := Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)
    let PM : SixMat := F.symm P
    PM * PM = PM := by
  dsimp only
  let F := Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)
  let PM : SixMat := F.symm P
  change PM * PM = PM
  apply F.injective
  rw [map_mul]
  change F PM * F PM = F PM
  rw [show F PM = P from F.apply_symm_apply P]
  exact hP

/-- Transport the signed residual scalar projection-square
identity to the literal original complex 6×6 matrix. -/
theorem sixMatrix_residualScalarSquare_transport
    (W : SixMat) (P : SixH →L[ℂ] SixH) (mu : ℂ)
    (hSq :
      (1 : SixH →L[ℂ] SixH) -
        W.toEuclideanLin.toContinuousLinearMap *
          W.toEuclideanLin.toContinuousLinearMap =
        (1 - mu) • P) :
    let F := Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)
    let PM : SixMat := F.symm P
    W * W = 1 - (1 - mu) • PM := by
  dsimp only
  let F := Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)
  let PM : SixMat := F.symm P
  change W * W = 1 - (1 - mu) • PM
  have hOp :
      F.symm ((1 : SixH →L[ℂ] SixH) - F W * F W) =
        F.symm ((1 - mu) • P) := by
    exact congrArg F.symm hSq
  have hMatrix :
      1 - W * W = (1 - mu) • PM := by
    simpa only [map_sub, map_one, map_mul, map_smul,
      F.symm_apply_apply] using hOp
  linear_combination -hMatrix

/-- Any genuine 6×6 witness of rank≤4 whose ambient Hilbert
square differs from identity by a scalar multiple of a
projection must have residual square scalar exactly zero. -/
theorem sixMatrix_rank_le_four_residualSquare_scalar_zero
    (W : SixMat)
    (P : SixH →L[ℂ] SixH) (mu : ℂ)
    (hRank : W.rank ≤ 4)
    (hP : P * P = P)
    (hSq :
      (1 : SixH →L[ℂ] SixH) -
        W.toEuclideanLin.toContinuousLinearMap *
          W.toEuclideanLin.toContinuousLinearMap =
        (1 - mu) • P) :
    mu = 0 := by
  let F := Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)
  let PM : SixMat := F.symm P
  have hPM : PM * PM = PM :=
    sixMatrix_residualProjection_transport_idempotent P hP
  have hSqM : W * W = 1 - (1 - mu) • PM :=
    sixMatrix_residualScalarSquare_transport W P mu hSq
  have hDefect := sixMatrix_rank_le_four_scalarProjection_defect_eq_one
    W PM (1 - mu) hRank hPM hSqM
  linear_combination -hDefect

end Neoplatonic.LTR
