import Neoplatonic.LTR.FiveDimensionalGradedZeroProduct
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# LTR-MAN-22: exact coordinate commutator products on a five-fibre square

A faithful multiplicity pattern (2,1,1,1) of the two-bit truth algebra
has a canonical Hilbert coordinate system indexed by Fin 5. The vertices
00, 01, 10, 11 occur at positions 0, 1, 2, 3; coordinate 4 is a
second copy of 00. Both truth-coordinate projections act diagonally.

For an arbitrary complex Dirac matrix D, define the coordinate
Hermitian commutators i[D,P] and i[D,Q] entrywise. These calculations
identify exact matrix entries of their two ordered products.
The opposite-corner and two-step-path identities remain valid even if
D couples all vertex pairs. They will feed the support obstruction.
-/

namespace Neoplatonic.LTR

/-- First Boolean coordinate in a five-coordinate faithful representation
with the 00 truth fibre duplicated at coordinate four. -/
def fiveFibreSquareP (j : Fin 5) : ℂ :=
  if j = 1 ∨ j = 3 then 1 else 0

/-- Second Boolean coordinate in the same multiplicity pattern. -/
def fiveFibreSquareQ (j : Fin 5) : ℂ :=
  if j = 2 ∨ j = 3 then 1 else 0

/-- The Hermitian first-coordinate Dirac commutator, entrywise. -/
def fiveFibreSquareA (D : Matrix (Fin 5) (Fin 5) ℂ) :
    Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => Complex.I * (fiveFibreSquareP j - fiveFibreSquareP i) * D i j

/-- The Hermitian second-coordinate Dirac commutator, entrywise. -/
def fiveFibreSquareB (D : Matrix (Fin 5) (Fin 5) ℂ) :
    Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => Complex.I * (fiveFibreSquareQ j - fiveFibreSquareQ i) * D i j

private theorem fiveFibreSquare_AB00 (D : Matrix (Fin 5) (Fin 5) ℂ) :
    (fiveFibreSquareA D * fiveFibreSquareB D) 0 0 = D 0 3 * D 3 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_five,
    fiveFibreSquareA, fiveFibreSquareB, fiveFibreSquareP, fiveFibreSquareQ,
    ← mul_assoc] <;> ring_nf <;> simp [Complex.I_sq]

private theorem fiveFibreSquare_AB44 (D : Matrix (Fin 5) (Fin 5) ℂ) :
    (fiveFibreSquareA D * fiveFibreSquareB D) 4 4 = D 4 3 * D 3 4 := by
  simp [Matrix.mul_apply, Fin.sum_univ_five,
    fiveFibreSquareA, fiveFibreSquareB, fiveFibreSquareP, fiveFibreSquareQ,
    ← mul_assoc] <;> ring_nf <;> simp [Complex.I_sq]

private theorem fiveFibreSquare_AB11 (D : Matrix (Fin 5) (Fin 5) ℂ) :
    (fiveFibreSquareA D * fiveFibreSquareB D) 1 1 = -(D 1 2 * D 2 1) := by
  simp [Matrix.mul_apply, Fin.sum_univ_five,
    fiveFibreSquareA, fiveFibreSquareB, fiveFibreSquareP, fiveFibreSquareQ,
    ← mul_assoc] <;> ring_nf <;> simp [Complex.I_sq]

private theorem fiveFibreSquare_AB03 (D : Matrix (Fin 5) (Fin 5) ℂ) :
    (fiveFibreSquareA D * fiveFibreSquareB D) 0 3 = -(D 0 1 * D 1 3) := by
  simp [Matrix.mul_apply, Fin.sum_univ_five,
    fiveFibreSquareA, fiveFibreSquareB, fiveFibreSquareP, fiveFibreSquareQ,
    ← mul_assoc] <;> ring_nf <;> simp [Complex.I_sq]

private theorem fiveFibreSquare_AB43 (D : Matrix (Fin 5) (Fin 5) ℂ) :
    (fiveFibreSquareA D * fiveFibreSquareB D) 4 3 = -(D 4 1 * D 1 3) := by
  simp [Matrix.mul_apply, Fin.sum_univ_five,
    fiveFibreSquareA, fiveFibreSquareB, fiveFibreSquareP, fiveFibreSquareQ,
    ← mul_assoc] <;> ring_nf <;> simp [Complex.I_sq]

private theorem fiveFibreSquare_BA03 (D : Matrix (Fin 5) (Fin 5) ℂ) :
    (fiveFibreSquareB D * fiveFibreSquareA D) 0 3 = -(D 0 2 * D 2 3) := by
  simp [Matrix.mul_apply, Fin.sum_univ_five,
    fiveFibreSquareA, fiveFibreSquareB, fiveFibreSquareP, fiveFibreSquareQ,
    ← mul_assoc] <;> ring_nf <;> simp [Complex.I_sq]

private theorem fiveFibreSquare_BA43 (D : Matrix (Fin 5) (Fin 5) ℂ) :
    (fiveFibreSquareB D * fiveFibreSquareA D) 4 3 = -(D 4 2 * D 2 3) := by
  simp [Matrix.mul_apply, Fin.sum_univ_five,
    fiveFibreSquareA, fiveFibreSquareB, fiveFibreSquareP, fiveFibreSquareQ,
    ← mul_assoc] <;> ring_nf <;> simp [Complex.I_sq]

private theorem fiveFibreSquare_BA12 (D : Matrix (Fin 5) (Fin 5) ℂ) :
    (fiveFibreSquareB D * fiveFibreSquareA D) 1 2 = D 1 3 * D 3 2 := by
  simp [Matrix.mul_apply, Fin.sum_univ_five,
    fiveFibreSquareA, fiveFibreSquareB, fiveFibreSquareP, fiveFibreSquareQ,
    ← mul_assoc] <;> ring_nf <;> simp [Complex.I_sq]

/-- With both ordered coordinate products zero, two opposite-corner
scalar couplings and the six one-dimensional-fibre path products obey
the necessary entrywise vanishing equations. -/
theorem fiveFibreSquare_product_zero_entries
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hAB : fiveFibreSquareA D * fiveFibreSquareB D = 0)
    (hBA : fiveFibreSquareB D * fiveFibreSquareA D = 0) :
    D 0 3 * D 3 0 = 0 ∧
    D 4 3 * D 3 4 = 0 ∧
    D 1 2 * D 2 1 = 0 ∧
    D 0 1 * D 1 3 = 0 ∧
    D 4 1 * D 1 3 = 0 ∧
    D 0 2 * D 2 3 = 0 ∧
    D 4 2 * D 2 3 = 0 ∧
    D 1 3 * D 3 2 = 0 := by
  have hab (i j : Fin 5) : (fiveFibreSquareA D * fiveFibreSquareB D) i j = 0 := by
    rw [hAB]; rfl
  have hba (i j : Fin 5) : (fiveFibreSquareB D * fiveFibreSquareA D) i j = 0 := by
    rw [hBA]; rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [fiveFibreSquare_AB00] using hab 0 0
  · simpa only [fiveFibreSquare_AB44] using hab 4 4
  · simpa only [fiveFibreSquare_AB11, neg_eq_zero] using hab 1 1
  · simpa only [fiveFibreSquare_AB03, neg_eq_zero] using hab 0 3
  · simpa only [fiveFibreSquare_AB43, neg_eq_zero] using hab 4 3
  · simpa only [fiveFibreSquare_BA03, neg_eq_zero] using hba 0 3
  · simpa only [fiveFibreSquare_BA43, neg_eq_zero] using hba 4 3
  · simpa only [fiveFibreSquare_BA12] using hba 1 2

end Neoplatonic.LTR
