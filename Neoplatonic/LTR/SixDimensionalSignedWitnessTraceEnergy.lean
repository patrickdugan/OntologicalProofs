import Neoplatonic.LTR.SixDimensionalSignedWitnessCornerWeights
import Mathlib.Tactic

/-!
# LTR-MAN-92: the genuine signed-witness trace fixes neutral fibre multiplicities

The universal complex matrix trace decomposition from MAN-92 combines
with the direct Boolean-square entry table for the actual plus and
minus coordinate commutators of a single Hermitian Dirac operator.

Under a genuine 6×6 matrix involution,

    6 = 2(m1+m2) + 8e03     for W+ = i[D,P+Q],
    6 = 2(m0+m3) + 8e12     for W- = i[D,P-Q].

Here e03 and e12 are the *oriented* real squared energies from
MAN-81/82, and the factor eight accounts for both orientations
and the doubled ±2i entry coefficient.

At the MAN-85 saturation e=1/4 the neutral pair has exactly two
basis coordinates. Faithfulness gives one basis coordinate in
each neutral truth atom, excluding adjacent-double truth patterns.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The plus-witness neutral subspace dimension is exactly the
sum of the 01 and 10 truth-fibre multiplicities. -/
theorem sixPlusNeutral_card_eq_fibreSum
    (label : Fin 6 → Fin 4) :
    (Finset.univ.filter (fun i : Fin 6 =>
      squarePlusNeutral (label i))).card =
      truthMultiplicity label 1 + truthMultiplicity label 2 := by
  classical
  let s1 : Finset (Fin 6) :=
    Finset.univ.filter (fun i => label i = 1)
  let s2 : Finset (Fin 6) :=
    Finset.univ.filter (fun i => label i = 2)
  have hd : Disjoint s1 s2 := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have h1 : label i = 1 := (Finset.mem_filter.mp hi).2
    have h2 : label i = 2 := (Finset.mem_filter.mp hj).2
    exact (by decide : (1 : Fin 4) ≠ 2) (h1.symm.trans h2)
  calc
    (Finset.univ.filter (fun i : Fin 6 =>
      squarePlusNeutral (label i))).card = (s1 ∪ s2).card := by
        congr 1
        change (Finset.univ.filter (fun i : Fin 6 =>
            label i = 1 ∨ label i = 2)) =
          (Finset.univ.filter (fun i : Fin 6 => label i = 1)) ∪
          (Finset.univ.filter (fun i : Fin 6 => label i = 2))
        exact Finset.filter_or
          (fun i : Fin 6 => label i = 0)
          (fun i : Fin 6 => label i = 3) Finset.univ
          (fun i : Fin 6 => label i = 1)
          (fun i : Fin 6 => label i = 2) Finset.univ
    _ = s1.card + s2.card := Finset.card_union_of_disjoint hd
    _ = truthMultiplicity label 1 + truthMultiplicity label 2 := rfl

/-- The minus-witness neutral sector dimension is the sum
of the 00 and 11 truth-fibre multiplicities. -/
theorem sixMinusNeutral_card_eq_fibreSum
    (label : Fin 6 → Fin 4) :
    (Finset.univ.filter (fun i : Fin 6 =>
      squareMinusNeutral (label i))).card =
      truthMultiplicity label 0 + truthMultiplicity label 3 := by
  classical
  let s0 : Finset (Fin 6) :=
    Finset.univ.filter (fun i => label i = 0)
  let s3 : Finset (Fin 6) :=
    Finset.univ.filter (fun i => label i = 3)
  have hd : Disjoint s0 s3 := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have h0 : label i = 0 := (Finset.mem_filter.mp hi).2
    have h3 : label i = 3 := (Finset.mem_filter.mp hj).2
    exact (by decide : (0 : Fin 4) ≠ 3) (h0.symm.trans h3)
  calc
    (Finset.univ.filter (fun i : Fin 6 =>
      squareMinusNeutral (label i))).card = (s0 ∪ s3).card := by
        congr 1
        change (Finset.univ.filter (fun i : Fin 6 =>
            label i = 0 ∨ label i = 3)) =
          (Finset.univ.filter (fun i : Fin 6 => label i = 0)) ∪
          (Finset.univ.filter (fun i : Fin 6 => label i = 3))
        exact Finset.filter_or
    _ = s0.card + s3.card := Finset.card_union_of_disjoint hd
    _ = truthMultiplicity label 0 + truthMultiplicity label 3 := rfl

/-- Exact trace identity for the true complex six-dimensional
plus witness whenever its matrix square is the identity. -/
theorem sixLabelled_plusWitness_involution_trace_energy
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hW :
      (labelledSquareA label D + labelledSquareB label D) *
        (labelledSquareA label D + labelledSquareB label D) = 1) :
    (6 : ℂ) =
      (2 : ℂ) *
        ((truthMultiplicity label 1 + truthMultiplicity label 2 : ℕ) : ℂ) +
      (8 : ℂ) * ((sixTruthFibreBlockEnergy label D 0 3 : ℝ) : ℂ) := by
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  have hnn : ∀ i j : Fin 6,
      squarePlusNeutral (label i) → squarePlusNeutral (label j) →
        W i j * W j i = 0 := by
    intro i j hi hj
    exact sixLabelled_plusWitness_neutral_pair_zero label D i j hi hj
  have htrace :=
    sixMatrix_involution_neutral_card_budget
      W (fun i => squarePlusNeutral (label i)) hnn hW
  change (6 : ℂ) =
    (2 : ℂ) * ((Finset.univ.filter
      (fun i : Fin 6 => squarePlusNeutral (label i))).card : ℂ) +
    (∑ i : Fin 6, ∑ j : Fin 6,
      if ¬squarePlusNeutral (label i) ∧
          ¬squarePlusNeutral (label j) then
        (labelledSquareA label D + labelledSquareB label D) i j *
          (labelledSquareA label D + labelledSquareB label D) j i
      else 0) at htrace
  rw [sixPlusNeutral_card_eq_fibreSum,
    sixLabelled_plusWitness_complement_energy,
    sixLabelled_opposite03Energy_eq_two_blockEnergy label D hD] at htrace
  calc
    (6 : ℂ) =
        (2 : ℂ) *
          ((truthMultiplicity label 1 + truthMultiplicity label 2 : ℕ) : ℂ) +
        (4 : ℂ) *
          ((2 : ℂ) * ((sixTruthFibreBlockEnergy label D 0 3 : ℝ) : ℂ)) :=
      htrace
    _ = _ := by ring

/-- The corresponding exact trace identity for the true
six-dimensional minus witness and opposite 01/10 Dirac energy. -/
theorem sixLabelled_minusWitness_involution_trace_energy
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hW :
      (labelledSquareA label D - labelledSquareB label D) *
        (labelledSquareA label D - labelledSquareB label D) = 1) :
    (6 : ℂ) =
      (2 : ℂ) *
        ((truthMultiplicity label 0 + truthMultiplicity label 3 : ℕ) : ℂ) +
      (8 : ℂ) * ((sixTruthFibreBlockEnergy label D 1 2 : ℝ) : ℂ) := by
  let W : SixMat := labelledSquareA label D - labelledSquareB label D
  have hnn : ∀ i j : Fin 6,
      squareMinusNeutral (label i) → squareMinusNeutral (label j) →
        W i j * W j i = 0 := by
    intro i j hi hj
    exact sixLabelled_minusWitness_neutral_pair_zero label D i j hi hj
  have htrace :=
    sixMatrix_involution_neutral_card_budget
      W (fun i => squareMinusNeutral (label i)) hnn hW
  change (6 : ℂ) =
    (2 : ℂ) * ((Finset.univ.filter
      (fun i : Fin 6 => squareMinusNeutral (label i))).card : ℂ) +
    (∑ i : Fin 6, ∑ j : Fin 6,
      if ¬squareMinusNeutral (label i) ∧
          ¬squareMinusNeutral (label j) then
        (labelledSquareA label D - labelledSquareB label D) i j *
          (labelledSquareA label D - labelledSquareB label D) j i
      else 0) at htrace
  rw [sixMinusNeutral_card_eq_fibreSum,
    sixLabelled_minusWitness_complement_energy,
    sixLabelled_opposite12Energy_eq_two_blockEnergy label D hD] at htrace
  calc
    (6 : ℂ) =
        (2 : ℂ) *
          ((truthMultiplicity label 0 + truthMultiplicity label 3 : ℕ) : ℂ) +
        (4 : ℂ) *
          ((2 : ℂ) * ((sixTruthFibreBlockEnergy label D 1 2 : ℝ) : ℂ)) :=
      htrace
    _ = _ := by ring

/-- The plus involution at e03=1/4 leaves exactly two Hilbert
coordinates across the 01 and 10 neutral truth atoms. -/
theorem sixLabelled_plusWitness_saturated_neutral_fibreSum_two
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hW :
      (labelledSquareA label D + labelledSquareB label D) *
        (labelledSquareA label D + labelledSquareB label D) = 1)
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ)) :
    truthMultiplicity label 1 + truthMultiplicity label 2 = 2 := by
  have hh := sixLabelled_plusWitness_involution_trace_energy
    label D hD hW
  rw [h03] at hh
  have hc :
      (((truthMultiplicity label 1 + truthMultiplicity label 2 : ℕ) : ℂ)) =
        (2 : ℂ) := by
    push_cast
    norm_num at hh
    linear_combination (-1 / 2 : ℂ) * hh
  exact_mod_cast hc

/-- The minus involution at e12=1/4 likewise gives precisely
two Hilbert coordinates across truth atoms 00 and 11. -/
theorem sixLabelled_minusWitness_saturated_neutral_fibreSum_two
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hW :
      (labelledSquareA label D - labelledSquareB label D) *
        (labelledSquareA label D - labelledSquareB label D) = 1)
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    truthMultiplicity label 0 + truthMultiplicity label 3 = 2 := by
  have hh := sixLabelled_minusWitness_involution_trace_energy
    label D hD hW
  rw [h12] at hh
  have hc :
      (((truthMultiplicity label 0 + truthMultiplicity label 3 : ℕ) : ℂ)) =
        (2 : ℂ) := by
    push_cast
    norm_num at hh
    linear_combination (-1 / 2 : ℂ) * hh
  exact_mod_cast hc

end Neoplatonic.LTR
