import Neoplatonic.LTR.FiveFibreConnesDualObstruction
import Mathlib.Tactic

/-!
# LTR-MAN-26: four truth-coordinate orientations of the five-fibre square

The multiplicity (2,1,1,1) representation is written with its doubled
vertex at coordinate 0 (and again at coordinate 4). Taking the doubled
vertex as logical 00, 01, 10, or 11 corresponds to independently
complementing the two coordinate projections.

Complementing a projection reverses the sign of its Hermitian Dirac
commutator. Consequently the zero-product identities and nonvanishing
hypotheses persist in all four orientations. MAN-25's explicit
opposite-corner Connes dual contradiction applies to each.

The theorem works in the canonical chart with the duplicated sector
in positions 0 and 4 and its opposite in position 3. A formal
unitary-basis reduction of arbitrary faithful representations to this
chart remains a separate obligation.
-/

namespace Neoplatonic.LTR

/-- Optionally complement the first truth-coordinate projection. -/
def fiveFibreSquareOrientedP (flip : Bool) (i : Fin 5) : ℂ :=
  if flip then 1 - fiveFibreSquareP i else fiveFibreSquareP i

/-- Optionally complement the second truth-coordinate projection. -/
def fiveFibreSquareOrientedQ (flip : Bool) (i : Fin 5) : ℂ :=
  if flip then 1 - fiveFibreSquareQ i else fiveFibreSquareQ i

/-- Hermitian coordinate commutator for the first oriented bit. -/
def fiveFibreSquareOrientedA (flip : Bool)
    (D : Matrix (Fin 5) (Fin 5) ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => Complex.I *
    (fiveFibreSquareOrientedP flip j - fiveFibreSquareOrientedP flip i) * D i j

/-- Hermitian coordinate commutator for the second oriented bit. -/
def fiveFibreSquareOrientedB (flip : Bool)
    (D : Matrix (Fin 5) (Fin 5) ℂ) : Matrix (Fin 5) (Fin 5) ℂ :=
  fun i j => Complex.I *
    (fiveFibreSquareOrientedQ flip j - fiveFibreSquareOrientedQ flip i) * D i j

/-- Bit complementation reverses the first coordinate commutator's sign. -/
theorem fiveFibreSquareOrientedA_eq
    (flip : Bool) (D : Matrix (Fin 5) (Fin 5) ℂ) :
    fiveFibreSquareOrientedA flip D =
      if flip then -fiveFibreSquareA D else fiveFibreSquareA D := by
  cases flip <;> ext i j <;>
    simp [fiveFibreSquareOrientedA, fiveFibreSquareOrientedP,
      fiveFibreSquareA, Matrix.neg_apply] <;> ring

/-- Bit complementation reverses the second coordinate commutator's sign. -/
theorem fiveFibreSquareOrientedB_eq
    (flip : Bool) (D : Matrix (Fin 5) (Fin 5) ℂ) :
    fiveFibreSquareOrientedB flip D =
      if flip then -fiveFibreSquareB D else fiveFibreSquareB D := by
  cases flip <;> ext i j <;>
    simp [fiveFibreSquareOrientedB, fiveFibreSquareOrientedQ,
      fiveFibreSquareB, Matrix.neg_apply] <;> ring

/-- All four combinations of coordinate complements retain the
ordered zero products and nonzero directional commutators. -/
theorem fiveFibreSquare_orientedProducts_to_canonical
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (flipP flipQ : Bool)
    (hAB : fiveFibreSquareOrientedA flipP D *
      fiveFibreSquareOrientedB flipQ D = 0)
    (hBA : fiveFibreSquareOrientedB flipQ D *
      fiveFibreSquareOrientedA flipP D = 0)
    (hA : fiveFibreSquareOrientedA flipP D ≠ 0)
    (hB : fiveFibreSquareOrientedB flipQ D ≠ 0) :
    fiveFibreSquareA D * fiveFibreSquareB D = 0 ∧
    fiveFibreSquareB D * fiveFibreSquareA D = 0 ∧
    fiveFibreSquareA D ≠ 0 ∧ fiveFibreSquareB D ≠ 0 := by
  cases flipP <;> cases flipQ
  all_goals
    simp only [fiveFibreSquareOrientedA_eq,
      fiveFibreSquareOrientedB_eq, Bool.false_eq_true, Bool.true_eq_true,
      ↓reduceIte] at hAB hBA hA hB
    simp_all only [neg_mul, mul_neg, neg_neg, neg_eq_zero,
      neg_ne_zero]

/-- The canonical dual Hamming obstruction holds in every Boolean
truth-coordinate orientation, with its duplicated sector at 0/4. -/
theorem fiveFibreSquare_fourOrientations_connesDual_noGo
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (flipP flipQ : Bool)
    (hD : ∀ i j, D i j = star (D j i))
    (hAB : fiveFibreSquareOrientedA flipP D *
      fiveFibreSquareOrientedB flipQ D = 0)
    (hBA : fiveFibreSquareOrientedB flipQ D *
      fiveFibreSquareOrientedA flipP D = 0)
    (hA : fiveFibreSquareOrientedA flipP D ≠ 0)
    (hB : fiveFibreSquareOrientedB flipQ D ≠ 0)
    (hdual : ∀ f : Fin 5 → ℂ, f 4 = f 0 →
      ‖(D * Matrix.diagonal f -
        Matrix.diagonal f * D).toEuclideanLin.toContinuousLinearMap‖ ≤ 1 →
      ‖f 0 - f 3‖ ≤ (2 : ℝ)) :
    False := by
  obtain ⟨hab, hba, ha, hb⟩ :=
    fiveFibreSquare_orientedProducts_to_canonical
      D flipP flipQ hAB hBA hA hB
  exact fiveFibreSquare_connesDual_hamming_noGo
    D hD hab hba ha hb hdual

end Neoplatonic.LTR
