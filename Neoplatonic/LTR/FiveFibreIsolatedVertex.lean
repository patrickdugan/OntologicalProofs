import Neoplatonic.LTR.FiveFibreHermitianSupport
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# LTR-MAN-24: a scalar truth fibre becomes isolated in the 5D square

Continue from the exact matrix entries of MAN-22 and the Hermitian
support restrictions of MAN-23. The 00 truth fibre is doubled, while
01, 10 and 11 are one-dimensional complex fibres.

If the coordinate Hermitian commutators A=i[D,p] and B=i[D,q]
are each nonzero and AB=BA=0, both singleton edges incident to
11 must vanish. The opposite-corner edges incident to 11 also vanish,
leaving its atomic indicator commuting with D.

Thus a separating nonconstant represented observable has zero Dirac
commutator. This contradicts the finite-distance kernel-constancy
condition for the opposite vertices 00 and 11. Deriving this condition
from the full Connes dual metric and transporting the result through
all four multiplicity patterns are subsequent formal steps.
-/

namespace Neoplatonic.LTR

private theorem fiveFibreSquare_A_zero_of_edge13
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hD : ∀ i j, D i j = star (D j i))
    (hAB : fiveFibreSquareA D * fiveFibreSquareB D = 0)
    (hBA : fiveFibreSquareB D * fiveFibreSquareA D = 0)
    (hc : D 1 3 ≠ 0) :
    fiveFibreSquareA D = 0 := by
  obtain ⟨h03, h43, h12⟩ :=
    fiveFibreSquare_oppositeCouplings_zero D hD hAB hBA
  obtain ⟨h01, h41, h23⟩ :=
    (fiveFibreSquare_singletonBranches D hD hAB hBA).1 hc
  have h30 : D 3 0 = 0 := by simpa [h03] using hD 3 0
  have h34 : D 3 4 = 0 := by simpa [h43] using hD 3 4
  have h21 : D 2 1 = 0 := by simpa [h12] using hD 2 1
  have h10 : D 1 0 = 0 := by simpa [h01] using hD 1 0
  have h14 : D 1 4 = 0 := by simpa [h41] using hD 1 4
  have h32 : D 3 2 = 0 := by simpa [h23] using hD 3 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fiveFibreSquareA, fiveFibreSquareP,
      h03, h43, h12, h01, h41, h23,
      h30, h34, h21, h10, h14, h32]

private theorem fiveFibreSquare_B_zero_of_edge23
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hD : ∀ i j, D i j = star (D j i))
    (hAB : fiveFibreSquareA D * fiveFibreSquareB D = 0)
    (hBA : fiveFibreSquareB D * fiveFibreSquareA D = 0)
    (hd : D 2 3 ≠ 0) :
    fiveFibreSquareB D = 0 := by
  obtain ⟨h03, h43, h12⟩ :=
    fiveFibreSquare_oppositeCouplings_zero D hD hAB hBA
  obtain ⟨h02, h42, h13⟩ :=
    (fiveFibreSquare_singletonBranches D hD hAB hBA).2 hd
  have h30 : D 3 0 = 0 := by simpa [h03] using hD 3 0
  have h34 : D 3 4 = 0 := by simpa [h43] using hD 3 4
  have h21 : D 2 1 = 0 := by simpa [h12] using hD 2 1
  have h20 : D 2 0 = 0 := by simpa [h02] using hD 2 0
  have h24 : D 2 4 = 0 := by simpa [h42] using hD 2 4
  have h31 : D 3 1 = 0 := by simpa [h13] using hD 3 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fiveFibreSquareB, fiveFibreSquareQ,
      h03, h43, h12, h02, h42, h13,
      h30, h34, h21, h20, h24, h31]

/-- If both coordinate commutators are nonzero, the three singleton
vertices cannot support a nonzero square edge incident to 11.
All Dirac couplings between truth sector 11 and other sectors vanish. -/
theorem fiveFibreSquare_vertex11_isolated
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hD : ∀ i j, D i j = star (D j i))
    (hAB : fiveFibreSquareA D * fiveFibreSquareB D = 0)
    (hBA : fiveFibreSquareB D * fiveFibreSquareA D = 0)
    (hA : fiveFibreSquareA D ≠ 0)
    (hB : fiveFibreSquareB D ≠ 0) :
    D 0 3 = 0 ∧ D 4 3 = 0 ∧
      D 1 3 = 0 ∧ D 2 3 = 0 := by
  obtain ⟨h03, h43, -⟩ :=
    fiveFibreSquare_oppositeCouplings_zero D hD hAB hBA
  have h13 : D 1 3 = 0 := by
    by_contra hc
    exact hA (fiveFibreSquare_A_zero_of_edge13 D hD hAB hBA hc)
  have h23 : D 2 3 = 0 := by
    by_contra hd
    exact hB (fiveFibreSquare_B_zero_of_edge23 D hD hAB hBA hd)
  exact ⟨h03, h43, h13, h23⟩

/-- The atomic 11 projection, which is nonconstant on the 00 and 11
truth fibres, in the five-coordinate faithful representation. -/
def fiveFibreSquareVertex11 (i : Fin 5) : ℂ :=
  if i = 3 then 1 else 0

/-- Commutator of a Dirac matrix with the 11 truth indicator, as an
actual product of finite matrices. -/
theorem fiveFibreSquare_vertex11_commutes
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hD : ∀ i j, D i j = star (D j i))
    (h03 : D 0 3 = 0) (h43 : D 4 3 = 0)
    (h13 : D 1 3 = 0) (h23 : D 2 3 = 0) :
    D * Matrix.diagonal fiveFibreSquareVertex11 =
      Matrix.diagonal fiveFibreSquareVertex11 * D := by
  have h30 : D 3 0 = 0 := by simpa [h03] using hD 3 0
  have h34 : D 3 4 = 0 := by simpa [h43] using hD 3 4
  have h31 : D 3 1 = 0 := by simpa [h13] using hD 3 1
  have h32 : D 3 2 = 0 := by simpa [h23] using hD 3 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_diagonal, Matrix.diagonal_mul,
      fiveFibreSquareVertex11, h03, h43, h13, h23,
      h30, h34, h31, h32]

/-- A nonconstant represented truth indicator in the Dirac commutator
kernel contradicts the finite-distance kernel-constancy requirement.

This is the canonical multiplicity (2,1,1,1) obstruction with the
metric's kernel-constancy consequence stated explicitly as a premise. -/
theorem fiveFibreSquare_noFiniteOppositeMetric
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hD : ∀ i j, D i j = star (D j i))
    (hAB : fiveFibreSquareA D * fiveFibreSquareB D = 0)
    (hBA : fiveFibreSquareB D * fiveFibreSquareA D = 0)
    (hA : fiveFibreSquareA D ≠ 0)
    (hB : fiveFibreSquareB D ≠ 0)
    (hkernel : ∀ f : Fin 5 → ℂ,
      f 4 = f 0 →
      D * Matrix.diagonal f = Matrix.diagonal f * D →
      f 0 = f 3) :
    False := by
  obtain ⟨h03, h43, h13, h23⟩ :=
    fiveFibreSquare_vertex11_isolated D hD hAB hBA hA hB
  have hc := fiveFibreSquare_vertex11_commutes D hD h03 h43 h13 h23
  have heq : fiveFibreSquareVertex11 0 = fiveFibreSquareVertex11 3 :=
    hkernel fiveFibreSquareVertex11 (by norm_num [fiveFibreSquareVertex11]) hc
  norm_num [fiveFibreSquareVertex11] at heq

end Neoplatonic.LTR
