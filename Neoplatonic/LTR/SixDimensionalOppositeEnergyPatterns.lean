import Neoplatonic.LTR.SixDimensionalTruthBlockHermitianEnergy
import Mathlib.Tactic

/-!
# LTR-MAN-83: numerical opposite-corner energy cases for faithful six-dimensional truth spectra

MAN-82 bounds the squared energy of each Hermitian opposite-corner
Dirac block using one quarter of the smaller of the two truth-fibre
multiplicities. MAN-55 completely classifies every faithful
six-dimensional diagonal representation into ten labelled patterns.

Evaluating the two opposite-pair minima on those ten patterns yields
only three possibilities: (1,1), (2,1), or (1,2).
The (2,2) case would cost at least eight Hilbert dimensions.

Combining the pattern classification with the exact-Hamming block
bounds yields three explicit possible energy regions:

    E03 ≤ 1/4 and E12 ≤ 1/4,
    E03 ≤ 1/2 and E12 ≤ 1/4,
    E03 ≤ 1/4 and E12 ≤ 1/2.

Consequently E03 + E12 ≤ 3/4 and at least one of the opposite
blocks has energy at most 1/4. These are the oriented squared
entry energies; the MAN-78 signed trace uses both orientations.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A faithful six-dimensional truth spectrum has only three
possible ordered pairs of opposite-corner minimum multiplicities. -/
theorem sixTruthOppositeMinimums_threeCases
    (label : Fin 6 → Fin 4)
    (hsurj : Function.Surjective label) :
    (min (truthMultiplicity label 0) (truthMultiplicity label 3) = 1 ∧
      min (truthMultiplicity label 1) (truthMultiplicity label 2) = 1) ∨
    (min (truthMultiplicity label 0) (truthMultiplicity label 3) = 2 ∧
      min (truthMultiplicity label 1) (truthMultiplicity label 2) = 1) ∨
    (min (truthMultiplicity label 0) (truthMultiplicity label 3) = 1 ∧
      min (truthMultiplicity label 1) (truthMultiplicity label 2) = 2) := by
  have hp := truthMultiplicity6_complete label hsurj
  simp only [truthMultiplicityPattern6] at hp
  rcases hp with h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨h0, h1, h2, h3⟩
  all_goals simp [h0, h1, h2, h3]

/-- For a faithful six-dimensional truth representation, the sum
of the two opposite-pair minimum multiplicities is at most three. -/
theorem sixTruthOppositeMinimums_sum_le_three
    (label : Fin 6 → Fin 4)
    (hsurj : Function.Surjective label) :
    min (truthMultiplicity label 0) (truthMultiplicity label 3) +
      min (truthMultiplicity label 1) (truthMultiplicity label 2) ≤ 3 := by
  rcases sixTruthOppositeMinimums_threeCases label hsurj with
    ⟨h03, h12⟩ | ⟨h03, h12⟩ | ⟨h03, h12⟩
  all_goals simp [h03, h12]

/-- Under the exact complex Connes Hamming metric and faithfulness,
the two opposite-corner block energies must lie in one of three
numerically explicit rectangles in the energy plane. -/
theorem sixLabelled_exactHamming_oppositeEnergy_threeCases
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    (sixTruthFibreBlockEnergy label D 0 3 ≤ (1 / 4 : ℝ) ∧
      sixTruthFibreBlockEnergy label D 1 2 ≤ (1 / 4 : ℝ)) ∨
    (sixTruthFibreBlockEnergy label D 0 3 ≤ (1 / 2 : ℝ) ∧
      sixTruthFibreBlockEnergy label D 1 2 ≤ (1 / 4 : ℝ)) ∨
    (sixTruthFibreBlockEnergy label D 0 3 ≤ (1 / 4 : ℝ) ∧
      sixTruthFibreBlockEnergy label D 1 2 ≤ (1 / 2 : ℝ)) := by
  obtain ⟨h03, h12⟩ :=
    sixLabelled_exactHamming_oppositeBlock_minEnergy
      label D hD hham
  rcases sixTruthOppositeMinimums_threeCases label hsurj with
    ⟨hm03, hm12⟩ | ⟨hm03, hm12⟩ | ⟨hm03, hm12⟩
  · exact Or.inl ⟨by simpa [hm03] using h03,
      by simpa [hm12] using h12⟩
  · exact Or.inr (Or.inl ⟨by
      calc
        sixTruthFibreBlockEnergy label D 0 3 ≤ (2 : ℝ) / 4 := by
          simpa [hm03] using h03
        _ = 1 / 2 := by norm_num,
      by simpa [hm12] using h12⟩)
  · exact Or.inr (Or.inr ⟨by simpa [hm03] using h03,
      by
        calc
          sixTruthFibreBlockEnergy label D 1 2 ≤ (2 : ℝ) / 4 := by
            simpa [hm12] using h12
          _ = 1 / 2 := by norm_num⟩)

/-- The sum of both oriented opposite-truth-pair squared coupling
energies is bounded by three quarters in every faithful six-dimensional
exact-Hamming Hermitian Dirac representation. -/
theorem sixLabelled_exactHamming_oppositeEnergy_sum_le_threeQuarters
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    sixTruthFibreBlockEnergy label D 0 3 +
      sixTruthFibreBlockEnergy label D 1 2 ≤ (3 / 4 : ℝ) := by
  rcases sixLabelled_exactHamming_oppositeEnergy_threeCases
    label D hsurj hD hham with
    ⟨h03, h12⟩ | ⟨h03, h12⟩ | ⟨h03, h12⟩
  all_goals linarith

/-- At least one of the two opposite-corner Dirac blocks has squared
coupling energy at most one quarter, whatever the faithful six-dimensional
truth-fibre multiplicity pattern. -/
theorem sixLabelled_exactHamming_oneOppositeEnergy_le_quarter
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    sixTruthFibreBlockEnergy label D 0 3 ≤ (1 / 4 : ℝ) ∨
      sixTruthFibreBlockEnergy label D 1 2 ≤ (1 / 4 : ℝ) := by
  rcases sixLabelled_exactHamming_oppositeEnergy_threeCases
    label D hsurj hD hham with
    ⟨h03, h12⟩ | ⟨h03, h12⟩ | ⟨h03, h12⟩
  · exact Or.inl h03
  · exact Or.inr h12
  · exact Or.inl h03

end Neoplatonic.LTR
