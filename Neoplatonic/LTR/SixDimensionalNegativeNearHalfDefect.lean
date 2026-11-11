import Neoplatonic.LTR.SixDimensionalSignedBitFlipTransport
import Neoplatonic.LTR.SixDimensionalRealPauliDefectLeakage
import Mathlib.Tactic

/-!
# LTR-MAN-151: mirror the quantitative signed defect by first-bit translation

MAN-148 proves the *same* original Dirac matrix under first-bit
truth translation has W_+'=-W_-, while the neutral projections
are exchanged. Translation permutes E03 and E12, so the genuine
real residual Pauli overlap changes sign.

MAN-147's positive near-half signed defect can consequently be
applied to a negative overlap c<=0, with -c>=1/2-epsilon.
It bounds the actual minus signed witness directly:
  ||I-(A-B)^2|| <= 2 epsilon.

This is an exact original-coordinate finite 6D matrix theorem;
it does not assume pure saturation or a canonical residual chart.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Translation by the first truth bit negates the original
oriented opposite Dirac-energy imbalance exactly. -/
theorem sixOrientedOppositeEnergyImbalance_translationOne_neg
    (label : Fin 6 → Fin 4) (D : SixMat) :
    sixOrientedOppositeEnergyImbalance
        (twoBitSquareTranslation 1 ∘ label) D =
      -sixOrientedOppositeEnergyImbalance label D := by
  let tau := twoBitSquareTranslation 1
  obtain ⟨ht0, ht1, ht2, ht3⟩ := twoBitSquareTranslation_one_values
  have h03 :
      sixTruthFibreBlockEnergy (tau ∘ label) D 0 3 =
        sixTruthFibreBlockEnergy label D 1 2 := by
    have h := sixTruthFibreBlockEnergy_truthEquiv tau label D 1 2
    rw [ht1, ht2] at h
    exact h
  have h12 :
      sixTruthFibreBlockEnergy (tau ∘ label) D 1 2 =
        sixTruthFibreBlockEnergy label D 0 3 := by
    have h := sixTruthFibreBlockEnergy_truthEquiv tau label D 0 3
    rw [ht0, ht3] at h
    exact h
  change (2 : ℝ) *
      (sixTruthFibreBlockEnergy (tau ∘ label) D 0 3 -
        sixTruthFibreBlockEnergy (tau ∘ label) D 1 2) =
    -(2 * (sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2))
  rw [h03, h12]
  ring

/-- Near maximal negative Pauli overlap, the original *minus*
signed six-dimensional Dirac matrix has small spectral defect. -/
theorem sixLabelled_exactHamming_negativeNearHalf_minusDefect_norm_le
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (epsilon : ℝ)
    (hc : sixOrientedOppositeEnergyImbalance label D ≤ 0)
    (hnear : (1 / 2 : ℝ) - epsilon ≤
      -sixOrientedOppositeEnergyImbalance label D) :
    let Wminus := labelledSquareA label D - labelledSquareB label D
    ‖(1 : SixMat) - Wminus * Wminus‖ ≤ 2 * epsilon := by
  let tau := twoBitSquareTranslation 1
  have hham' : ∀ u v : Fin 4,
      sixLabelledConnesDistance (tau ∘ label) D u v =
        (twoBitSquareHamming u v : ℝ≥0∞) :=
    sixLabelled_exactHamming_truthTranslation label D 1 hham
  have hsign :
      sixOrientedOppositeEnergyImbalance (tau ∘ label) D =
        -sixOrientedOppositeEnergyImbalance label D :=
    sixOrientedOppositeEnergyImbalance_translationOne_neg label D
  have hc' : 0 ≤
      sixOrientedOppositeEnergyImbalance (tau ∘ label) D := by
    rw [hsign]
    linarith
  have hnear' : (1 / 2 : ℝ) - epsilon ≤
      sixOrientedOppositeEnergyImbalance (tau ∘ label) D := by
    rw [hsign]
    exact hnear
  have hBound :=
    sixLabelled_exactHamming_positiveNearHalf_defect_norm_le
      (tau ∘ label) D hD hham' epsilon hc' hnear'
  dsimp only at hBound ⊢
  have hW :
      labelledSquareA (tau ∘ label) D +
        labelledSquareB (tau ∘ label) D =
      -(labelledSquareA label D - labelledSquareB label D) :=
    sixLabelled_plusWitness_translationOne_eq_negMinus label D
  rw [hW] at hBound
  simpa only [neg_mul, mul_neg, neg_neg] using hBound

end Neoplatonic.LTR
