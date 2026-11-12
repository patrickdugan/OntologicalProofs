import Neoplatonic.LTR.SixDimensionalNearHalfSingleton00ProbeNoGo
import Neoplatonic.LTR.SixDimensionalPositiveNearHalfOppositeDoubleNoGo
import Neoplatonic.LTR.SixDimensionalTruthRelabelSaturation
import Neoplatonic.LTR.SixDimensionalNegativeNearHalfDefect
import Mathlib.Tactic

/-!
# LTR-MAN-171: quantitative signed Pauli overlap exclusion in all faithful six-dimensional charts

MAN-162 forces m01=m10=1 for positive overlap c>=1/2-1/250.
The opposite truth multiplicity sum is therefore four. MAN-167
excludes the (2,2) opposite-double pattern and MAN-170 excludes
any singleton-00 pattern.

Boolean-square complementation τ=translation by 11 swaps 00/11
while preserving the oriented imbalance c, and transfers the
singleton-00 obstruction to a singleton-11 obstruction.

Translation by the first truth bit τ=translation by 01 negates c
and carries a positive near-endpoint obstruction to its negative
mirror. The resulting genuine full 6D condition is

  |c| < 1/2 - 1/250 = 62/125.

This excludes a uniform quantitative collar around both forbidden
signed Pauli endpoints, for one original Hermitian Dirac operator
and every faithful six-dimensional label assignment.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Complementing both Boolean truth bits transports the
singleton-00 near-half probe obstruction to a singleton-11
obstruction for the same original Hermitian Dirac matrix. -/
theorem sixLabelled_exactHamming_positiveNearHalf_singleton11_impossible
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm3 : truthMultiplicity label 3 = 1)
    (hnear : (1 / 2 : ℝ) - (1 / 250 : ℝ) ≤
      sixOrientedOppositeEnergyImbalance label D) :
    False := by
  let tau := twoBitSquareTranslation 3
  obtain ⟨ht0, ht1, ht2, ht3⟩ :=
    twoBitSquareTranslation_three_values
  have hm0' : truthMultiplicity (tau ∘ label) 0 = 1 := by
    have h := sixTruthMultiplicity_truthEquiv tau label 3
    rw [ht3] at h
    exact h.trans hm3
  have hham' :
      ∀ u v : Fin 4,
        sixLabelledConnesDistance (tau ∘ label) D u v =
          (twoBitSquareHamming u v : ℝ≥0∞) :=
    sixLabelled_exactHamming_truthTranslation label D 3 hham
  have h03' :
      sixTruthFibreBlockEnergy (tau ∘ label) D 0 3 =
        sixTruthFibreBlockEnergy label D 0 3 := by
    have h := sixTruthFibreBlockEnergy_truthEquiv tau label D 3 0
    rw [ht3, ht0] at h
    exact h.trans
      (sixTruthFibreBlockEnergy_reverse label D hD 0 3).symm
  have h12' :
      sixTruthFibreBlockEnergy (tau ∘ label) D 1 2 =
        sixTruthFibreBlockEnergy label D 1 2 := by
    have h := sixTruthFibreBlockEnergy_truthEquiv tau label D 2 1
    rw [ht2, ht1] at h
    exact h.trans
      (sixTruthFibreBlockEnergy_reverse label D hD 1 2).symm
  have hc' :
      sixOrientedOppositeEnergyImbalance (tau ∘ label) D =
        sixOrientedOppositeEnergyImbalance label D := by
    dsimp [sixOrientedOppositeEnergyImbalance]
    rw [h03', h12']
  have hnear' : (1 / 2 : ℝ) - (1 / 250 : ℝ) ≤
      sixOrientedOppositeEnergyImbalance (tau ∘ label) D := by
    rw [hc']
    exact hnear
  exact sixLabelled_exactHamming_positiveNearHalf_singleton00_impossible
    (tau ∘ label) D hD hham' hm0' hnear'

/-- Every positive near-half Pauli overlap is excluded in the
original faithful six-dimensional exact-Hamming Dirac chart. -/
theorem sixLabelled_exactHamming_positiveNearHalf_uniform_impossible
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hnear : (1 / 2 : ℝ) - (1 / 250 : ℝ) ≤
      sixOrientedOppositeEnergyImbalance label D) :
    False := by
  obtain ⟨hm1, hm2⟩ :=
    sixLabelled_exactHamming_positiveNearHalf_neutralSingletons
      label D hsurj hD hham (1 / 250 : ℝ) hnear
      (by norm_num)
  have hsum : truthMultiplicity label 0 +
      truthMultiplicity label 1 +
      truthMultiplicity label 2 +
      truthMultiplicity label 3 = 6 := by
    simpa only [Fin.sum_univ_four] using truthMultiplicity_sum label
  have hpos0 := truthMultiplicity_pos label hsurj 0
  have hpos3 := truthMultiplicity_pos label hsurj 3
  by_cases hm0 : truthMultiplicity label 0 = 1
  · exact sixLabelled_exactHamming_positiveNearHalf_singleton00_impossible
      label D hD hham hm0 hnear
  by_cases hm3 : truthMultiplicity label 3 = 1
  · exact sixLabelled_exactHamming_positiveNearHalf_singleton11_impossible
      label D hD hham hm3 hnear
  have hm0two : truthMultiplicity label 0 = 2 := by omega
  have hm3two : truthMultiplicity label 3 = 2 := by omega
  exact sixLabelled_exactHamming_positiveNearHalf_oppositeDouble_impossible
    label D hsurj hD hham hm0two hm1 hm2 hm3two hnear

/-- First-bit translation transfers the uniform positive
near-half exclusion to negative signed Pauli overlap. -/
theorem sixLabelled_exactHamming_negativeNearHalf_uniform_impossible
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hnear : (1 / 2 : ℝ) - (1 / 250 : ℝ) ≤
      -sixOrientedOppositeEnergyImbalance label D) :
    False := by
  let tau := twoBitSquareTranslation 1
  have hsurj' : Function.Surjective (tau ∘ label) := by
    intro u
    obtain ⟨i, hi⟩ := hsurj (tau.symm u)
    refine ⟨i, ?_⟩
    change tau (label i) = u
    rw [hi, Equiv.apply_symm_apply]
  have hham' :
      ∀ u v : Fin 4,
        sixLabelledConnesDistance (tau ∘ label) D u v =
          (twoBitSquareHamming u v : ℝ≥0∞) :=
    sixLabelled_exactHamming_truthTranslation label D 1 hham
  have hc' :
      sixOrientedOppositeEnergyImbalance (tau ∘ label) D =
        -sixOrientedOppositeEnergyImbalance label D :=
    sixOrientedOppositeEnergyImbalance_translationOne_neg label D
  have hnear' : (1 / 2 : ℝ) - (1 / 250 : ℝ) ≤
      sixOrientedOppositeEnergyImbalance (tau ∘ label) D := by
    rw [hc']
    exact hnear
  exact sixLabelled_exactHamming_positiveNearHalf_uniform_impossible
    (tau ∘ label) D hsurj' hD hham' hnear'

/-- An explicit uniform margin around both real Pauli endpoint
values for any faithful exact-Hamming six-dimensional Dirac chart:
|c| < 62/125, with c=2(E03-E12). -/
theorem sixLabelled_exactHamming_realPauliMixed_abs_lt_62over125
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    |sixOrientedOppositeEnergyImbalance label D| <
      (62 / 125 : ℝ) := by
  let c : ℝ := sixOrientedOppositeEnergyImbalance label D
  have hNum : (1 / 2 : ℝ) - (1 / 250 : ℝ) =
      (62 / 125 : ℝ) := by norm_num
  have hUpper : c < (62 / 125 : ℝ) := by
    by_contra hn
    have hnear : (1 / 2 : ℝ) - (1 / 250 : ℝ) ≤ c := by
      rw [hNum]
      exact le_of_not_gt hn
    exact sixLabelled_exactHamming_positiveNearHalf_uniform_impossible
      label D hsurj hD hham hnear
  have hLower : -c < (62 / 125 : ℝ) := by
    by_contra hn
    have hnear : (1 / 2 : ℝ) - (1 / 250 : ℝ) ≤ -c := by
      rw [hNum]
      exact le_of_not_gt hn
    exact sixLabelled_exactHamming_negativeNearHalf_uniform_impossible
      label D hsurj hD hham hnear
  change |c| < (62 / 125 : ℝ)
  exact abs_lt.mpr ⟨by linarith, hUpper⟩

end Neoplatonic.LTR
