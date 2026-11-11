import Neoplatonic.LTR.SixDimensionalNeutralTraceDecomposition
import Mathlib.Tactic

/-!
# LTR-MAN-92: exact Boolean-square witness corner coefficients

On the truth square in order 00,01,10,11, the plus coordinate
witness W+=i[D,P]+i[D,Q] vanishes between the two truth atoms
01,10. Its only nonzero interactions within the complementary
truth sector {00,11} are the 00↔11 entries, with coefficient ±2i.

The minus coordinate witness W-=i[D,P]-i[D,Q] exchanges the two
sectors. Its neutral sector is {00,11} and its only nonzero
complementary-sector entries are 01↔10, again coefficient ±2i.

A direct 4×4 finite truth-table proof certifies that the product
W_ij W_ji has coefficient 4 on the surviving opposite pair,
without introducing a Hermiticity assumption or replacing the
actual common Dirac matrix.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The 01,10 truth sector on which the plus witness has a zero
internal block. -/
def squarePlusNeutral (u : Fin 4) : Prop := u = 1 ∨ u = 2

/-- The 00,11 truth sector on which the minus witness has a zero
internal block. -/
def squareMinusNeutral (u : Fin 4) : Prop := u = 0 ∨ u = 3

/-- Whole first-coordinate plus second-coordinate witness vanishes
between neutral truth atoms 01 and 10. -/
theorem sixLabelled_plusWitness_neutral_pair_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (i j : Fin 6)
    (hi : squarePlusNeutral (label i))
    (hj : squarePlusNeutral (label j)) :
    (labelledSquareA label D + labelledSquareB label D) i j *
      (labelledSquareA label D + labelledSquareB label D) j i = 0 := by
  rcases hi with hi | hi <;> rcases hj with hj | hj <;>
    simp [squarePlusNeutral, Matrix.add_apply,
      labelledSquareA, labelledSquareB,
      squareTruthBitP, squareTruthBitQ, hi, hj] <;> ring

/-- The minus witness has zero internal block on the 00 and 11
truth atoms. -/
theorem sixLabelled_minusWitness_neutral_pair_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (i j : Fin 6)
    (hi : squareMinusNeutral (label i))
    (hj : squareMinusNeutral (label j)) :
    (labelledSquareA label D - labelledSquareB label D) i j *
      (labelledSquareA label D - labelledSquareB label D) j i = 0 := by
  rcases hi with hi | hi <;> rcases hj with hj | hj <;>
    simp [squareMinusNeutral, Matrix.sub_apply,
      labelledSquareA, labelledSquareB,
      squareTruthBitP, squareTruthBitQ, hi, hj] <;> ring

/-- The product of coefficients for the plus witness, restricted
to the complementary 00,11 sector, is exactly 4 on the oriented
00↔11 opposite corners and zero everywhere else. -/
theorem squarePlusWitness_complement_product_truthTable
    (u v : Fin 4) (x y : ℂ) :
    (if ¬squarePlusNeutral u ∧ ¬squarePlusNeutral v then
      (Complex.I * (squareTruthBitP v - squareTruthBitP u) * x +
       Complex.I * (squareTruthBitQ v - squareTruthBitQ u) * x) *
      (Complex.I * (squareTruthBitP u - squareTruthBitP v) * y +
       Complex.I * (squareTruthBitQ u - squareTruthBitQ v) * y)
    else 0) =
      (4 : ℂ) *
        ((if (u = 0 ∧ v = 3) ∨ (u = 3 ∧ v = 0)
          then (1 : ℂ) else 0) * x * y) := by
  fin_cases u <;> fin_cases v <;>
    norm_num [squarePlusNeutral, squareTruthBitP, squareTruthBitQ,
      Complex.I_mul_I] <;> ring_nf <;>
    norm_num [Complex.I_mul_I, pow_two]

/-- The corresponding minus-witness weight is 4 on the
01↔10 opposite pair and zero on all other complement entries. -/
theorem squareMinusWitness_complement_product_truthTable
    (u v : Fin 4) (x y : ℂ) :
    (if ¬squareMinusNeutral u ∧ ¬squareMinusNeutral v then
      (Complex.I * (squareTruthBitP v - squareTruthBitP u) * x -
       Complex.I * (squareTruthBitQ v - squareTruthBitQ u) * x) *
      (Complex.I * (squareTruthBitP u - squareTruthBitP v) * y -
       Complex.I * (squareTruthBitQ u - squareTruthBitQ v) * y)
    else 0) =
      (4 : ℂ) *
        ((if (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1)
          then (1 : ℂ) else 0) * x * y) := by
  fin_cases u <;> fin_cases v <;>
    norm_num [squareMinusNeutral, squareTruthBitP, squareTruthBitQ,
      Complex.I_mul_I] <;> ring_nf <;>
    norm_num [Complex.I_mul_I, pow_two]

/-- The actual six-dimensional plus witness has precisely the
opposite-00/11 complementary ordered quadratic entries. -/
theorem sixLabelled_plusWitness_complement_product
    (label : Fin 6 → Fin 4) (D : SixMat)
    (i j : Fin 6) :
    (if ¬squarePlusNeutral (label i) ∧
        ¬squarePlusNeutral (label j) then
      (labelledSquareA label D + labelledSquareB label D) i j *
        (labelledSquareA label D + labelledSquareB label D) j i
    else 0) =
      (4 : ℂ) *
        ((if (label i = 0 ∧ label j = 3) ∨
          (label i = 3 ∧ label j = 0) then (1 : ℂ) else 0) *
          D i j * D j i) := by
  simpa only [Matrix.add_apply, labelledSquareA, labelledSquareB]
    using squarePlusWitness_complement_product_truthTable
      (label i) (label j) (D i j) (D j i)

/-- The minus witness's complementary ordered quadratic entries
are four times the original Dirac product on 01↔10. -/
theorem sixLabelled_minusWitness_complement_product
    (label : Fin 6 → Fin 4) (D : SixMat)
    (i j : Fin 6) :
    (if ¬squareMinusNeutral (label i) ∧
        ¬squareMinusNeutral (label j) then
      (labelledSquareA label D - labelledSquareB label D) i j *
        (labelledSquareA label D - labelledSquareB label D) j i
    else 0) =
      (4 : ℂ) *
        ((if (label i = 1 ∧ label j = 2) ∨
          (label i = 2 ∧ label j = 1) then (1 : ℂ) else 0) *
          D i j * D j i) := by
  simpa only [Matrix.sub_apply, labelledSquareA, labelledSquareB]
    using squareMinusWitness_complement_product_truthTable
      (label i) (label j) (D i j) (D j i)

/-- Total plus-witness complementary trace contribution is four
times MAN-78's bidirectional opposite 00/11 Dirac energy. -/
theorem sixLabelled_plusWitness_complement_energy
    (label : Fin 6 → Fin 4) (D : SixMat) :
    (∑ i : Fin 6, ∑ j : Fin 6,
      if ¬squarePlusNeutral (label i) ∧
          ¬squarePlusNeutral (label j) then
        (labelledSquareA label D + labelledSquareB label D) i j *
          (labelledSquareA label D + labelledSquareB label D) j i
      else 0) = (4 : ℂ) * labelledOpposite03Energy label D := by
  unfold labelledOpposite03Energy
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact sixLabelled_plusWitness_complement_product label D i j

/-- Total minus-witness complementary trace contribution is four
times the bidirectional opposite 01/10 Dirac energy. -/
theorem sixLabelled_minusWitness_complement_energy
    (label : Fin 6 → Fin 4) (D : SixMat) :
    (∑ i : Fin 6, ∑ j : Fin 6,
      if ¬squareMinusNeutral (label i) ∧
          ¬squareMinusNeutral (label j) then
        (labelledSquareA label D - labelledSquareB label D) i j *
          (labelledSquareA label D - labelledSquareB label D) j i
      else 0) = (4 : ℂ) * labelledOpposite12Energy label D := by
  unfold labelledOpposite12Energy
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact sixLabelled_minusWitness_complement_product label D i j

end Neoplatonic.LTR
