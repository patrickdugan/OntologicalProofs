import Neoplatonic.LTR.SixDimensionalPositiveMaxImbalanceNoGo
import Neoplatonic.LTR.SixDimensionalTruthRelabelSaturation
import Neoplatonic.LTR.SixDimensionalExactHammingPauliSaturation
import Mathlib.Tactic

/-!
# LTR-MAN-138: strict Pauli imbalance in exact 6D Hamming charts

MAN-85 proved the universal non-strict bound
    |E03-E12| <= 1/4.

MAN-137 eliminated positive equality in the genuine original
six-coordinate Dirac representation. Translating the four truth
atoms by the first Boolean bit exchanges the two opposite-corner
energy blocks, preserves all exact Connes-Hamming distances, and
keeps the same Hermitian Dirac matrix. Thus negative equality
is eliminated as well.

The surviving necessary condition is the STRICT inequality
    |E03-E12| < 1/4.

This is a new exact-Hamming obstruction for arbitrary faithful
six-dimensional truth labellings. It does not eliminate configurations
with strict imbalance and does not establish d_min >= 7.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The original true Dirac block energies cannot attain maximal
negative residual Pauli overlap. -/
theorem sixLabelled_exactHamming_maxNegativeImbalance_impossible
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hneg : sixTruthFibreBlockEnergy label D 1 2 -
        sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ)) :
    False := by
  let τ := twoBitSquareTranslation 1
  obtain ⟨ht0, ht1, ht2, ht3⟩ := twoBitSquareTranslation_one_values
  have hsurj' : Function.Surjective (τ ∘ label) := by
    intro u
    obtain ⟨i, hi⟩ := hsurj (τ.symm u)
    refine ⟨i, ?_⟩
    change τ (label i) = u
    rw [hi, Equiv.apply_symm_apply]
  have hham' :
      ∀ u v : Fin 4,
        sixLabelledConnesDistance (τ ∘ label) D u v =
          (twoBitSquareHamming u v : ℝ≥0∞) :=
    sixLabelled_exactHamming_truthTranslation label D 1 hham
  have he03' :
      sixTruthFibreBlockEnergy (τ ∘ label) D 0 3 =
        sixTruthFibreBlockEnergy label D 1 2 := by
    have h := sixTruthFibreBlockEnergy_truthEquiv τ label D 1 2
    rw [ht1, ht2] at h
    exact h
  have he12' :
      sixTruthFibreBlockEnergy (τ ∘ label) D 1 2 =
        sixTruthFibreBlockEnergy label D 0 3 := by
    have h := sixTruthFibreBlockEnergy_truthEquiv τ label D 0 3
    rw [ht0, ht3] at h
    exact h
  have hpositive :
      sixTruthFibreBlockEnergy (τ ∘ label) D 0 3 -
        sixTruthFibreBlockEnergy (τ ∘ label) D 1 2 =
          (1 / 4 : ℝ) := by
    rw [he03', he12']
    exact hneg
  exact sixLabelled_exactHamming_maxPositiveImbalance_impossible
    (τ ∘ label) D hsurj' hD hham' hpositive

/-- MAN-85's universal sharp Pauli residual bound is strict
for every actual faithful complex 6D exact-Hamming representation. -/
theorem sixLabelled_exactHamming_oppositeEnergyDiff_abs_lt_quarter
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    |sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2| < (1 / 4 : ℝ) := by
  have hbound :=
    sixLabelled_exactHamming_oppositeEnergyDiff_abs_le_quarter
      label D hD hham
  by_contra hnot
  have hge :
      (1 / 4 : ℝ) ≤
      |sixTruthFibreBlockEnergy label D 0 3 -
        sixTruthFibreBlockEnergy label D 1 2| :=
    le_of_not_gt hnot
  have heq :
      |sixTruthFibreBlockEnergy label D 0 3 -
        sixTruthFibreBlockEnergy label D 1 2| = (1 / 4 : ℝ) :=
    le_antisymm hbound hge
  rcases le_total 0
    (sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2) with hpos | hneg
  · have hsign :
        sixTruthFibreBlockEnergy label D 0 3 -
          sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ) := by
      simpa only [abs_of_nonneg hpos] using heq
    exact sixLabelled_exactHamming_maxPositiveImbalance_impossible
      label D hsurj hD hham hsign
  · have hsign :
        sixTruthFibreBlockEnergy label D 1 2 -
          sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ) := by
      rw [abs_of_nonpos hneg] at heq
      linarith
    exact sixLabelled_exactHamming_maxNegativeImbalance_impossible
      label D hsurj hD hham hsign

end Neoplatonic.LTR
