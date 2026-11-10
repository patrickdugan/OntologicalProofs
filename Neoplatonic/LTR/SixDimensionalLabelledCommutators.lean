import Neoplatonic.LTR.SixDimensionalTruthFibreBranching
import Neoplatonic.LTR.IdempotentGradingPairing
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# LTR-MAN-74: actual labelled-square coordinate commutators

A faithful four-truth-atom diagonal representation on Fin n is a
surjective map label : Fin n → Fin 4. Define the two coordinate
projections and the true Dirac imaginary commutators

  A = i[D, P],  B = i[D, Q].

The same arbitrary Hermitian Dirac matrix appears in both operators.
Their entrywise supports can overlap only between opposite vertices
(00,11) and (01,10) of the Boolean square. In particular, if D has
no opposite-corner entries, trace(A B) vanishes exactly, even if
the ordered operator products A B and B A are nonzero.

This is an analytic bridge from a concrete labelled representation
toward MAN-72's residual real Pauli mixed coefficient. Identifying
the ambient product trace with its two-dimensional residual product
trace is a distinct subsequent obligation.
-/

namespace Neoplatonic.LTR

/-- First bit of a truth atom in square order 00,01,10,11,
matching the existing canonical five-fibre convention. -/
def squareTruthBitP (v : Fin 4) : ℂ :=
  if v = 1 ∨ v = 3 then 1 else 0

/-- Second bit of a truth atom. -/
def squareTruthBitQ (v : Fin 4) : ℂ :=
  if v = 2 ∨ v = 3 then 1 else 0

/-- The two bits change simultaneously exactly on the two
opposite-corner diagonals, in either orientation. -/
def squareTruthOpposite (u v : Fin 4) : Prop :=
  (u = 0 ∧ v = 3) ∨ (u = 3 ∧ v = 0) ∨
  (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1)

theorem squareTruthOpposite_iff_bits (u v : Fin 4) :
    squareTruthOpposite u v ↔
      squareTruthBitP u ≠ squareTruthBitP v ∧
      squareTruthBitQ u ≠ squareTruthBitQ v := by
  fin_cases u <;> fin_cases v <;>
    simp [squareTruthOpposite, squareTruthBitP, squareTruthBitQ]

/-- The actual represented first-coordinate Boolean projection. -/
def labelledSquarePMatrix {n : ℕ} (label : Fin n → Fin 4) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => squareTruthBitP (label i))

/-- The actual represented second-coordinate projection. -/
def labelledSquareQMatrix {n : ℕ} (label : Fin n → Fin 4) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => squareTruthBitQ (label i))

/-- First imaginary coordinate commutator of the SAME Dirac matrix. -/
def labelledSquareA {n : ℕ} (label : Fin n → Fin 4)
    (D : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => Complex.I *
    (squareTruthBitP (label j) - squareTruthBitP (label i)) * D i j

/-- Second imaginary coordinate commutator. -/
def labelledSquareB {n : ℕ} (label : Fin n → Fin 4)
    (D : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j => Complex.I *
    (squareTruthBitQ (label j) - squareTruthBitQ (label i)) * D i j

theorem labelledSquareA_eq_diagonal_commutator {n : ℕ}
    (label : Fin n → Fin 4) (D : Matrix (Fin n) (Fin n) ℂ) :
    labelledSquareA label D =
      Complex.I • (D * labelledSquarePMatrix label -
        labelledSquarePMatrix label * D) := by
  ext i j
  simp [labelledSquareA, labelledSquarePMatrix,
    Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem labelledSquareB_eq_diagonal_commutator {n : ℕ}
    (label : Fin n → Fin 4) (D : Matrix (Fin n) (Fin n) ℂ) :
    labelledSquareB label D =
      Complex.I • (D * labelledSquareQMatrix label -
        labelledSquareQMatrix label * D) := by
  ext i j
  simp [labelledSquareB, labelledSquareQMatrix,
    Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Every represented coordinate commutator has zero diagonal. -/
theorem labelledSquareA_diag_zero {n : ℕ}
    (label : Fin n → Fin 4) (D : Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) : labelledSquareA label D i i = 0 := by
  simp [labelledSquareA]

theorem labelledSquareB_diag_zero {n : ℕ}
    (label : Fin n → Fin 4) (D : Matrix (Fin n) (Fin n) ℂ)
    (i : Fin n) : labelledSquareB label D i i = 0 := by
  simp [labelledSquareB]

theorem labelledSquareA_trace_zero {n : ℕ}
    (label : Fin n → Fin 4) (D : Matrix (Fin n) (Fin n) ℂ) :
    (labelledSquareA label D).trace = 0 := by
  change (∑ i : Fin n, labelledSquareA label D i i) = 0
  simp [labelledSquareA_diag_zero]

theorem labelledSquareB_trace_zero {n : ℕ}
    (label : Fin n → Fin 4) (D : Matrix (Fin n) (Fin n) ℂ) :
    (labelledSquareB label D).trace = 0 := by
  change (∑ i : Fin n, labelledSquareB label D i i) = 0
  simp [labelledSquareB_diag_zero]

/-- The first coordinate matrix vanishes on an entry when the first
Boolean truth coordinate is unchanged. -/
theorem labelledSquareA_entry_zero_of_bit_same {n : ℕ}
    (label : Fin n → Fin 4) (D : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n)
    (h : squareTruthBitP (label i) = squareTruthBitP (label j)) :
    labelledSquareA label D i j = 0 := by
  simp [labelledSquareA, h]

theorem labelledSquareB_entry_zero_of_bit_same {n : ℕ}
    (label : Fin n → Fin 4) (D : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n)
    (h : squareTruthBitQ (label i) = squareTruthBitQ (label j)) :
    labelledSquareB label D i j = 0 := by
  simp [labelledSquareB, h]

/-- On an 00-to-11 opposite-corner entry, both imaginary coordinate
commutators use the same Dirac coupling. -/
theorem labelledSquare_opposite03_entry_equal {n : ℕ}
    (label : Fin n → Fin 4) (D : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) (hi : label i = 0) (hj : label j = 3) :
    labelledSquareA label D i j = labelledSquareB label D i j := by
  simp [labelledSquareA, labelledSquareB,
    squareTruthBitP, squareTruthBitQ, hi, hj]

/-- On an 01-to-10 diagonal, the imaginary coordinate commutator
entries have opposite signs. -/
theorem labelledSquare_opposite12_entry_negative {n : ℕ}
    (label : Fin n → Fin 4) (D : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) (hi : label i = 1) (hj : label j = 2) :
    labelledSquareA label D i j = -labelledSquareB label D i j := by
  simp [labelledSquareA, labelledSquareB,
    squareTruthBitP, squareTruthBitQ, hi, hj] <;> ring

/-- If the Dirac operator has no couplings between opposite truth
atoms, the opposite-order coordinate entries cannot overlap.
This statement uses actual Dirac matrix entries, not inferred
supports of arbitrary operators. -/
theorem labelledSquare_crossTerm_zero_of_noOpposite {n : ℕ}
    (label : Fin n → Fin 4) (D : Matrix (Fin n) (Fin n) ℂ)
    (hopp : ∀ i j : Fin n,
      squareTruthOpposite (label i) (label j) → D i j = 0)
    (i j : Fin n) :
    labelledSquareA label D i j * labelledSquareB label D j i = 0 := by
  by_cases hp :
      squareTruthBitP (label i) = squareTruthBitP (label j)
  · rw [labelledSquareA_entry_zero_of_bit_same label D i j hp]
    simp
  · by_cases hq :
        squareTruthBitQ (label i) = squareTruthBitQ (label j)
    · have hz := labelledSquareB_entry_zero_of_bit_same
        label D j i hq.symm
      rw [hz]
      simp
    · have hdiag : squareTruthOpposite (label i) (label j) :=
        (squareTruthOpposite_iff_bits _ _).2 ⟨hp, hq⟩
      have hz := hopp i j hdiag
      simp [labelledSquareA, hz]

/-- With no opposite-corner Dirac couplings, the trace of the true
mixed coordinate commutator product vanishes, even if neither full
ordered product is zero. -/
theorem labelledSquare_crossTrace_zero_of_noOpposite {n : ℕ}
    (label : Fin n → Fin 4) (D : Matrix (Fin n) (Fin n) ℂ)
    (hopp : ∀ i j : Fin n,
      squareTruthOpposite (label i) (label j) → D i j = 0) :
    (labelledSquareA label D * labelledSquareB label D).trace = 0 := by
  change (∑ i : Fin n,
    (labelledSquareA label D * labelledSquareB label D) i i) = 0
  simp only [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j hj
  exact labelledSquare_crossTerm_zero_of_noOpposite label D hopp i j

end Neoplatonic.LTR
