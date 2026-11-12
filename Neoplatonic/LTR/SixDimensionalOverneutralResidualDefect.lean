import Neoplatonic.LTR.SixDimensionalOverneutralSignedRank
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-175: rank deficiency forces full scalar residual defect

Suppose W is a genuine six-dimensional complex matrix with
  W² = I - t P,   P²=P.
This is exactly the scalar-residual spectral-defect form from
MAN-144/145, after transporting the orthogonal residual projection
back to the original Hilbert coordinates.

For t≠1, W² has an EXPLICIT algebraic right inverse:

  (I-tP)⁻¹ = I + (t/(1-t)) P.

Consequently rank W=6. If instead rank W≤4, the scalar residual
defect coefficient is forced to t=1, so W²=I-P.

This is a purely finite complex matrix theorem. It needs no
operator-norm estimates and remains valid in the full interior
Pauli overlap region.

MAN-174 supplies rank Wminus≤4 whenever m01=m10=1.
The next original-coordinate bridge transports the exact residual
spectral projector from MAN-144 for the negative signed witness,
then identifies t=1-muMinus to obtain muMinus=0.
-/

namespace Neoplatonic.LTR

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- An idempotent P makes 1-tP explicitly right-invertible for
every scalar t≠1, by an elementary finite-matrix identity. -/
theorem sixMatrix_scalarProjection_defect_rightInverse
    (P : SixMat) (t : ℂ)
    (hP : P * P = P) (ht : t ≠ 1) :
    (1 - t • P) * (1 + (t / (1 - t)) • P) = 1 := by
  have hden : (1 : ℂ) - t ≠ 0 := by
    intro hz
    exact ht (sub_eq_zero.mp hz).symm
  let k : ℂ := t / (1 - t)
  have hCoeff : k - t - t * k = 0 := by
    dsimp [k]
    field_simp
    ring
  change (1 - t • P) * (1 + k • P) = 1
  calc
    (1 - t • P) * (1 + k • P) =
        1 + k • P - t • P - (t * k) • (P * P) := by
          calc
            _ = 1 + k • P -
                (t • P + t • (P * (k • P))) := by
                  simp only [sub_mul, mul_add, one_mul,
                    mul_one, Matrix.smul_mul]
                  abel
            _ = 1 + k • P - t • P -
                (t * k) • (P * P) := by
                  rw [Matrix.mul_smul, smul_smul]
                  abel
    _ = 1 + (k - t - t * k) • P := by
      rw [hP]
      module
    _ = 1 := by rw [hCoeff]; simp

/-- In six complex Hilbert coordinates, scalar-projection
square defect W²=I-tP and t≠1 forces full matrix rank 6. -/
theorem sixMatrix_scalarProjection_defect_fullRank
    (W P : SixMat) (t : ℂ)
    (hP : P * P = P)
    (hSq : W * W = 1 - t • P)
    (ht : t ≠ 1) :
    W.rank = 6 := by
  let R : SixMat := 1 + (t / (1 - t)) • P
  have hRight : (W * W) * R = 1 := by
    rw [hSq]
    exact sixMatrix_scalarProjection_defect_rightInverse P t hP ht
  have hRank1 : (1 : SixMat).rank = 6 := by
    norm_num [Matrix.rank_one]
  have hLower : 6 ≤ W.rank := by
    calc
      6 = ((W * W) * R).rank := by
        rw [hRight]
        exact hRank1.symm
      _ ≤ (W * W).rank := Matrix.rank_mul_le_left (W * W) R
      _ ≤ W.rank := Matrix.rank_mul_le_left W W
  exact le_antisymm (Matrix.rank_le_width W) hLower

/-- A rank-deficient original complex 6×6 witness with an
idempotent scalar spectral defect must have coefficient t=1. -/
theorem sixMatrix_rank_le_four_scalarProjection_defect_eq_one
    (W P : SixMat) (t : ℂ)
    (hRank : W.rank ≤ 4)
    (hP : P * P = P)
    (hSq : W * W = 1 - t • P) :
    t = 1 := by
  by_contra ht
  have hFull := sixMatrix_scalarProjection_defect_fullRank W P t hP hSq ht
  omega

/-- The overneutral negative signed witness forces full
residual annihilation whenever its original-coordinate square
has MAN-144's idempotent scalar residual-projection form. -/
theorem sixLabelled_minusWitness_overneutral_scalarDefect_eq_one
    (label : Fin 6 → Fin 4) (D P : SixMat)
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1)
    (t : ℂ)
    (hP : P * P = P)
    (hSq :
      (labelledSquareA label D - labelledSquareB label D) *
        (labelledSquareA label D - labelledSquareB label D) =
          1 - t • P) :
    t = 1 := by
  exact sixMatrix_rank_le_four_scalarProjection_defect_eq_one
    (labelledSquareA label D - labelledSquareB label D)
    P t
    (sixLabelled_minusWitness_rank_le_four_of_neutralSingletons
      label D hm1 hm2) hP hSq

end Neoplatonic.LTR
