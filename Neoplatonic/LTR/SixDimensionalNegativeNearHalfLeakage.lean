import Neoplatonic.LTR.SixDimensionalNegativeNearHalfDefect
import Neoplatonic.LTR.SixDimensionalRealPauliDefectLeakage
import Neoplatonic.LTR.SixDimensionalSignedBitFlipTransport
import Mathlib.Tactic

/-!
# LTR-MAN-152: mirrored negative-signed corner-neutral leakage

MAN-148 certifies that truth translation by 01 sends the genuine
positive signed 6D witness to minus the original negative witness,
and its neutral projector to the original minus-neutral projector.

Consequently MAN-147's two operator-norm estimates transport to
the negative residual Pauli overlap, with exactly the same 2ε
constant, still in the original six-dimensional Dirac chart:

  ||X_- Y_-|| <= 2ε,
  ||Y_-† Y_- - Q_-|| <= 2ε.

The sign cancels in both products. No saturated-energy premise,
canonical basis, or new analytic axiom is required.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- For a negative real Pauli overlap c<=0 close to -1/2,
the genuine minus signed witness has near-orthogonal corner and
neutral blocks in the original complex six-dimensional chart. -/
theorem sixLabelled_exactHamming_negativeNearHalf_cornerLeakage
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
    let Qminus := sixTruthSectorProjection label squareMinusNeutral
    let Cminus := (1 - Qminus : SixMat)
    let Xminus := Cminus * Wminus * Cminus
    let Yminus := Cminus * Wminus * Qminus
    ‖Xminus * Yminus‖ ≤ 2 * epsilon ∧
      ‖Yminus.conjTranspose * Yminus - Qminus‖ ≤ 2 * epsilon := by
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
    sixLabelled_exactHamming_positiveNearHalf_cornerLeakage
      (tau ∘ label) D hD hham' epsilon hc' hnear'
  dsimp only at hBound ⊢
  have hW :
      labelledSquareA (tau ∘ label) D +
        labelledSquareB (tau ∘ label) D =
      -(labelledSquareA label D - labelledSquareB label D) :=
    sixLabelled_plusWitness_translationOne_eq_negMinus label D
  have hQ :
      sixTruthSectorProjection (tau ∘ label) squarePlusNeutral =
        sixTruthSectorProjection label squareMinusNeutral :=
    sixTruthPlusNeutralProjection_translationOne label
  rw [hW, hQ] at hBound
  let W : SixMat := labelledSquareA label D - labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squareMinusNeutral
  let C : SixMat := 1 - Q
  change
    ‖(C * (-W) * C) * (C * (-W) * Q)‖ ≤ 2 * epsilon ∧
      ‖(C * (-W) * Q).conjTranspose *
        (C * (-W) * Q) - Q‖ ≤ 2 * epsilon at hBound
  have hX : C * (-W) * C = -(C * W * C) := by noncomm_ring
  have hY : C * (-W) * Q = -(C * W * Q) := by noncomm_ring
  rw [hX, hY] at hBound
  have hProduct :
      (-(C * W * C)) * (-(C * W * Q)) =
        (C * W * C) * (C * W * Q) := by noncomm_ring
  have hGram :
      (-(C * W * Q)).conjTranspose * (-(C * W * Q)) =
        (C * W * Q).conjTranspose * (C * W * Q) := by
    rw [Matrix.conjTranspose_neg]
    noncomm_ring
  rw [hProduct, hGram] at hBound
  change ‖(C * W * C) * (C * W * Q)‖ ≤ 2 * epsilon ∧
    ‖(C * W * Q).conjTranspose * (C * W * Q) - Q‖ ≤ 2 * epsilon
  exact hBound

end Neoplatonic.LTR
