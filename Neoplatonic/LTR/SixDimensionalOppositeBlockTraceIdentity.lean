import Neoplatonic.LTR.SixDimensionalOppositeEnergyPatterns
import Neoplatonic.LTR.SixDimensionalOppositeCornerPauliBudget
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# LTR-MAN-84: the exact signed mixed trace is twice the real block-energy difference

MAN-78 expresses the mixed Dirac coordinate-commutator trace as the
difference of its two bidirectional opposite-corner quadratic sums.
MAN-81/82 express the oriented whole-block energy as a real sum of
squared complex entry magnitudes.

For Hermitian D, Dᵢⱼ Dⱼᵢ = ‖Dᵢⱼ‖². Each bidirectional sum consists
of two equal oriented sums, because switching i,j preserves the
quadratic term and exchanges the two directions of the corner pair.

This supplies the formerly missing mathematical identification

    Tr(i[D,P] i[D,Q]) = 2 * (e03 - e12),

where e03 and e12 are the *actual* oriented whole-block squared
coupling energies, and the right side is embedded as a real complex
number. No metric assumptions are needed for this identity.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Real squared complex modulus is exactly the Hermitian
quadratic product z · z*, cast to a complex scalar. -/
theorem complex_cast_norm_sq_eq_mul_star (z : ℂ) :
    ((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z := by
  simpa [Complex.star_def] using (Complex.mul_conj' z).symm

/-- The oriented Dirac product over truth fibres u→v. -/
noncomputable def sixOrientedTruthProduct
    (label : Fin 6 → Fin 4) (D : SixMat)
    (u v : Fin 4) : ℂ :=
  ∑ i : Fin 6, ∑ j : Fin 6,
    if label i = u ∧ label j = v then D i j * D j i else 0

/-- The actual real squared entry energy of a compressed truth
block equals its oriented Hermitian Dirac quadratic product. -/
theorem sixTruthFibreBlockEnergy_cast_eq_orientedProduct
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (u v : Fin 4) :
    ((sixTruthFibreBlockEnergy label D u v : ℝ) : ℂ) =
      sixOrientedTruthProduct label D u v := by
  unfold sixTruthFibreBlockEnergy sixOrientedTruthProduct
  rw [Finset.sum_comm]
  push_cast
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [sixTruthFibreBlock_entry]
  by_cases h : label i = u ∧ label j = v
  · simp only [if_pos h]
    rw [hD j i]
    simpa using complex_cast_norm_sq_eq_mul_star (D i j)
  · simp [h]

/-- Exchanging the two truth fibres preserves the oriented sum
of the quadratic Dirac products, without a Hermiticity premise. -/
theorem sixOrientedTruthProduct_reverse
    (label : Fin 6 → Fin 4) (D : SixMat)
    (u v : Fin 4) :
    sixOrientedTruthProduct label D u v =
      sixOrientedTruthProduct label D v u := by
  unfold sixOrientedTruthProduct
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : label j = u ∧ label i = v
  · simp [h, mul_comm]
  · have h' : ¬(label i = v ∧ label j = u) := by
      simpa [and_comm] using h
    simp [h, h']

/-- The contribution from both directions of two distinct truth
fibres is exactly twice one oriented Dirac quadratic sum. -/
theorem sixTruthPair_bidirectional_eq_two_oriented
    (label : Fin 6 → Fin 4) (D : SixMat)
    (u v : Fin 4) (huv : u ≠ v) :
    (∑ i : Fin 6, ∑ j : Fin 6,
      (if (label i = u ∧ label j = v) ∨
          (label i = v ∧ label j = u) then (1 : ℂ) else 0) *
        D i j * D j i) =
      (2 : ℂ) * sixOrientedTruthProduct label D u v := by
  have hsplit :
      (∑ i : Fin 6, ∑ j : Fin 6,
        (if (label i = u ∧ label j = v) ∨
            (label i = v ∧ label j = u) then (1 : ℂ) else 0) *
          D i j * D j i) =
      sixOrientedTruthProduct label D u v +
        sixOrientedTruthProduct label D v u := by
    unfold sixOrientedTruthProduct
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h1 : label i = u ∧ label j = v
    · have h2 : ¬(label i = v ∧ label j = u) := by
        intro h
        apply huv
        calc
          u = label i := h1.1.symm
          _ = v := h.1
      simp [h1, h2, huv]
    · by_cases h2 : label i = v ∧ label j = u <;>
        simp [h1, h2, huv]
  rw [hsplit, ← sixOrientedTruthProduct_reverse label D u v]
  ring

/-- MAN-78's full bidirectional 00↔11 quadratic energy is twice
the complex embedding of the genuine 00→11 squared entry energy. -/
theorem sixLabelled_opposite03Energy_eq_two_blockEnergy
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    labelledOpposite03Energy label D =
      (2 : ℂ) * ((sixTruthFibreBlockEnergy label D 0 3 : ℝ) : ℂ) := by
  calc
    labelledOpposite03Energy label D =
        (2 : ℂ) * sixOrientedTruthProduct label D 0 3 :=
      sixTruthPair_bidirectional_eq_two_oriented label D 0 3 (by decide)
    _ = (2 : ℂ) *
        ((sixTruthFibreBlockEnergy label D 0 3 : ℝ) : ℂ) := by
      rw [sixTruthFibreBlockEnergy_cast_eq_orientedProduct label D hD]

/-- MAN-78's full bidirectional 01↔10 quadratic energy is twice
the complex embedding of its oriented block's squared entry energy. -/
theorem sixLabelled_opposite12Energy_eq_two_blockEnergy
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    labelledOpposite12Energy label D =
      (2 : ℂ) * ((sixTruthFibreBlockEnergy label D 1 2 : ℝ) : ℂ) := by
  calc
    labelledOpposite12Energy label D =
        (2 : ℂ) * sixOrientedTruthProduct label D 1 2 :=
      sixTruthPair_bidirectional_eq_two_oriented label D 1 2 (by decide)
    _ = (2 : ℂ) *
        ((sixTruthFibreBlockEnergy label D 1 2 : ℝ) : ℂ) := by
      rw [sixTruthFibreBlockEnergy_cast_eq_orientedProduct label D hD]

/-- The true mixed coordinate-commutator trace is the complex
embedding of twice the difference of the two oriented squared
opposite-corner block energies of the same Hermitian Dirac matrix. -/
theorem sixLabelled_crossTrace_eq_two_orientedEnergyDifference
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    (labelledSquareA label D * labelledSquareB label D).trace =
      ((2 * (sixTruthFibreBlockEnergy label D 0 3 -
        sixTruthFibreBlockEnergy label D 1 2) : ℝ) : ℂ) := by
  rw [labelledSquare_crossTrace_eq_energyDifference,
    sixLabelled_opposite03Energy_eq_two_blockEnergy label D hD,
    sixLabelled_opposite12Energy_eq_two_blockEnergy label D hD]
  push_cast
  ring

end Neoplatonic.LTR
