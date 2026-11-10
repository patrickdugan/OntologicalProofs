import Neoplatonic.LTR.SixDimensionalExactHammingAttainment
import Mathlib.Tactic

/-!
# LTR-MAN-78: exact opposite-corner trace balance of labelled Dirac commutators

For the genuine first and second imaginary coordinate commutators
A = i[D,P], B = i[D,Q] of an arbitrary four-truth-atom diagonal
representation, the mixed trace is supported only on the two
opposite-corner pairs, 00↔11 and 01↔10.

The two opposite diagonals enter with opposite signs. This gives
an exact signed quadratic expression for trace(A B), with the same
Dirac matrix in both factors and with no finite-dimensional norm or
metric assumptions.

The six-dimensional MAN-75/76 bridge then identifies that trace with
the mixed Pauli coefficient of the genuine residual operators. The
opposite-corner coupling energy difference, rather than either
diagonal alone, determines their Pauli inner product.
-/

namespace Neoplatonic.LTR

/-- Signed characteristic of the two opposite truth-corner pairs.
The orientation of an opposite pair does not affect its sign. -/
def squareOppositeSignedWeight (u v : Fin 4) : ℂ :=
  (if (u = 0 ∧ v = 3) ∨ (u = 3 ∧ v = 0) then 1 else 0) -
    (if (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) then 1 else 0)

/-- The sign of the opposite-corner overlap is the product of
the signed differences of the two truth bits. -/
theorem squareOppositeSignedWeight_eq_bitDifferences
    (u v : Fin 4) :
    squareOppositeSignedWeight u v =
      (squareTruthBitP v - squareTruthBitP u) *
        (squareTruthBitQ v - squareTruthBitQ u) := by
  fin_cases u <;> fin_cases v <;>
    norm_num [squareOppositeSignedWeight, squareTruthBitP, squareTruthBitQ]

/-- The opposite-00/11 contribution to the mixed trace, over
both orientations of the pair. -/
noncomputable def labelledOpposite03Energy {n : ℕ}
    (label : Fin n → Fin 4)
    (D : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n,
    (if (label i = 0 ∧ label j = 3) ∨
        (label i = 3 ∧ label j = 0) then (1 : ℂ) else 0) *
      D i j * D j i

/-- The analogous opposite-01/10 contribution. -/
noncomputable def labelledOpposite12Energy {n : ℕ}
    (label : Fin n → Fin 4)
    (D : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n,
    (if (label i = 1 ∧ label j = 2) ∨
        (label i = 2 ∧ label j = 1) then (1 : ℂ) else 0) *
      D i j * D j i

/-- Every individual mixed coordinate product is the correctly
signed opposite-corner Dirac quadratic. -/
theorem labelledSquare_crossTerm_signed {n : ℕ}
    (label : Fin n → Fin 4)
    (D : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) :
    labelledSquareA label D i j * labelledSquareB label D j i =
      squareOppositeSignedWeight (label i) (label j) *
        D i j * D j i := by
  simp only [labelledSquareA, labelledSquareB]
  rw [squareOppositeSignedWeight_eq_bitDifferences]
  have hI : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
  calc
    (Complex.I *
        (squareTruthBitP (label j) - squareTruthBitP (label i)) * D i j) *
      (Complex.I *
        (squareTruthBitQ (label i) - squareTruthBitQ (label j)) * D j i) =
      -(Complex.I * Complex.I) *
        ((squareTruthBitP (label j) - squareTruthBitP (label i)) *
          (squareTruthBitQ (label j) - squareTruthBitQ (label i))) *
        D i j * D j i := by ring
    _ = ((squareTruthBitP (label j) - squareTruthBitP (label i)) *
          (squareTruthBitQ (label j) - squareTruthBitQ (label i))) *
        D i j * D j i := by rw [hI]; ring

/-- The mixed trace of two actual labelled coordinate commutators
is exactly a signed sum of opposite-corner quadratic terms. -/
theorem labelledSquare_crossTrace_signed {n : ℕ}
    (label : Fin n → Fin 4)
    (D : Matrix (Fin n) (Fin n) ℂ) :
    (labelledSquareA label D * labelledSquareB label D).trace =
      ∑ i : Fin n, ∑ j : Fin n,
        squareOppositeSignedWeight (label i) (label j) *
          D i j * D j i := by
  change (∑ i : Fin n, ∑ j : Fin n,
      labelledSquareA label D i j * labelledSquareB label D j i) = _
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact labelledSquare_crossTerm_signed label D i j

/-- Exact identity for the difference between the two opposite-
corner contributions, valid in every finite complex dimension. -/
theorem labelledSquare_crossTrace_eq_energyDifference {n : ℕ}
    (label : Fin n → Fin 4)
    (D : Matrix (Fin n) (Fin n) ℂ) :
    (labelledSquareA label D * labelledSquareB label D).trace =
      labelledOpposite03Energy label D -
        labelledOpposite12Energy label D := by
  rw [labelledSquare_crossTrace_signed]
  simp only [labelledOpposite03Energy, labelledOpposite12Energy,
    squareOppositeSignedWeight, sub_mul, Finset.sum_sub_distrib]

end Neoplatonic.LTR
