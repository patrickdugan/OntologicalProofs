import Neoplatonic.LTR.SixDimensionalNeutralCornerTripotence
import Neoplatonic.LTR.SixDimensionalSignedWitnessCornerWeights
import Mathlib.Tactic

/-!
# LTR-MAN-93: the actual signed-Hamming truth-corner compression is tripotent

MAN-92's finite truth table separates the 00,11 corner from the
01,10 neutral truth fibres for W+=i[D,P+Q], and reverses the sectors
for W-=i[D,P-Q].

The diagonal coordinate projection Q onto the neutral truth fibres
is idempotent. Its internal witness block QWQ vanishes entrywise.
Under the exact-Hamming quarter-energy saturation of MAN-91,
the actual W+ or W- matrix is involutive, so MAN-93's general
zero-neutral-block result gives the concrete polynomial equation

     (P W P)^3 = P W P,    P=I-Q,

where P is the actual corner truth-sector projection. The complete
6x6 matrix equation includes all duplicated coordinates.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Project onto the full six-dimensional coordinate subset
carrying truth labels inside a specified neutral sector. -/
def sixTruthSectorProjection
    (label : Fin 6 → Fin 4)
    (sector : Fin 4 → Prop) [DecidablePred sector] : SixMat :=
  Matrix.diagonal (fun i => if sector (label i) then (1 : ℂ) else 0)

/-- A diagonal 0/1 truth-sector projection is idempotent for any
label multiplicities, including all faithful six-dimensional charts. -/
theorem sixTruthSectorProjection_idempotent
    (label : Fin 6 → Fin 4)
    (sector : Fin 4 → Prop) [DecidablePred sector] :
    sixTruthSectorProjection label sector *
      sixTruthSectorProjection label sector =
    sixTruthSectorProjection label sector := by
  ext i j
  simp only [sixTruthSectorProjection, Matrix.diagonal_mul]
  by_cases hi : sector (label i)
  · simp [hi, Matrix.diagonal_apply]
  · simp [hi, Matrix.diagonal_apply]

/-- If the original witness has zero entries inside a truth
sector, its entire projected neutral block is zero. -/
theorem sixTruthSectorProjection_W_zero
    (label : Fin 6 → Fin 4)
    (sector : Fin 4 → Prop) [DecidablePred sector]
    (W : SixMat)
    (hNN : ∀ i j : Fin 6,
      sector (label i) → sector (label j) → W i j = 0) :
    sixTruthSectorProjection label sector * W *
      sixTruthSectorProjection label sector = 0 := by
  ext i j
  simp only [sixTruthSectorProjection,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : sector (label i)
  · by_cases hj : sector (label j)
    · simp [hi, hj, hNN i j hi hj]
    · simp [hi, hj]
  · simp [hi]

/-- The actual signed PLUS Hamming witness vanishes entrywise
on the entire 01,10 truth sector, including multiplicities. -/
theorem sixLabelled_plusWitness_neutral_entry_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (i j : Fin 6)
    (hi : squarePlusNeutral (label i))
    (hj : squarePlusNeutral (label j)) :
    (labelledSquareA label D + labelledSquareB label D) i j = 0 := by
  rcases hi with hi | hi <;> rcases hj with hj | hj <;>
    simp [Matrix.add_apply, labelledSquareA, labelledSquareB,
      squareTruthBitP, squareTruthBitQ, hi, hj] <;> ring

/-- The actual signed MINUS witness vanishes entrywise on the
entire 00,11 neutral truth sector. -/
theorem sixLabelled_minusWitness_neutral_entry_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (i j : Fin 6)
    (hi : squareMinusNeutral (label i))
    (hj : squareMinusNeutral (label j)) :
    (labelledSquareA label D - labelledSquareB label D) i j = 0 := by
  rcases hi with hi | hi <;> rcases hj with hj | hj <;>
    simp [Matrix.sub_apply, labelledSquareA, labelledSquareB,
      squareTruthBitP, squareTruthBitQ, hi, hj] <;> ring

/-- The true plus signed witness is Hermitian whenever the
underlying six-dimensional Dirac matrix is Hermitian. -/
theorem sixLabelled_plusWitness_isHermitian
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    (labelledSquareA label D + labelledSquareB label D).IsHermitian := by
  have hA : (labelledSquareA label D).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr
      (sixLabelledSquareA_selfAdjoint label D hD)
  have hB : (labelledSquareB label D).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr
      (sixLabelledSquareB_selfAdjoint label D hD)
  exact hA.add hB

/-- The actual minus signed witness is likewise Hermitian. -/
theorem sixLabelled_minusWitness_isHermitian
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    (labelledSquareA label D - labelledSquareB label D).IsHermitian := by
  have hA : (labelledSquareA label D).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr
      (sixLabelledSquareA_selfAdjoint label D hD)
  have hB : (labelledSquareB label D).IsHermitian :=
    Matrix.isHermitian_iff_isSelfAdjoint.mpr
      (sixLabelledSquareB_selfAdjoint label D hD)
  exact hA.sub hB

/-- At 00↔11 saturated Dirac energy, the corner-to-corner block
of the actual plus witness is tripotent in the full complex
six-dimensional Hilbert coordinate algebra. -/
theorem sixLabelled_exactHamming_saturated03_corner_tripotent
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    sixComplementCornerBlock W Q *
      sixComplementCornerBlock W Q *
        sixComplementCornerBlock W Q =
      sixComplementCornerBlock W Q := by
  dsimp only
  apply sixMatrix_involution_zeroNeutral_corner_tripotent
  · exact sixLabelled_exactHamming_saturated03_trueMatrixPlus_involution
      label D hD hham h03 h12
  · exact sixTruthSectorProjection_idempotent label squarePlusNeutral
  · exact sixTruthSectorProjection_W_zero
      label squarePlusNeutral _ (sixLabelled_plusWitness_neutral_entry_zero label D)

/-- At 01↔10 saturated energy, the corner-to-corner block
of the actual difference witness obeys the same cubic equation. -/
theorem sixLabelled_exactHamming_saturated12_corner_tripotent
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = 0)
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    let W := labelledSquareA label D - labelledSquareB label D
    let Q := sixTruthSectorProjection label squareMinusNeutral
    sixComplementCornerBlock W Q *
      sixComplementCornerBlock W Q *
        sixComplementCornerBlock W Q =
      sixComplementCornerBlock W Q := by
  dsimp only
  apply sixMatrix_involution_zeroNeutral_corner_tripotent
  · exact sixLabelled_exactHamming_saturated12_trueMatrixMinus_involution
      label D hD hham h03 h12
  · exact sixTruthSectorProjection_idempotent label squareMinusNeutral
  · exact sixTruthSectorProjection_W_zero
      label squareMinusNeutral _ (sixLabelled_minusWitness_neutral_entry_zero label D)

/-- At 00↔11 saturation, the full complementary corner parts
of the neutral 01,10 columns are exactly orthonormal. -/
theorem sixLabelled_exactHamming_saturated03_neutral_isometry
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (j k : Fin 6)
    (hj : squarePlusNeutral (label j))
    (hk : squarePlusNeutral (label k)) :
    (∑ i : Fin 6,
      if ¬squarePlusNeutral (label i) then
        star ((labelledSquareA label D + labelledSquareB label D) i j) *
          (labelledSquareA label D + labelledSquareB label D) i k
      else 0) = if j = k then (1 : ℂ) else 0 := by
  exact sixMatrix_involution_neutralColumns_orthonormal
    (labelledSquareA label D + labelledSquareB label D)
    (fun i => squarePlusNeutral (label i))
    (sixLabelled_exactHamming_saturated03_trueMatrixPlus_involution label D hD hham h03 h12)
    (sixLabelled_plusWitness_isHermitian label D hD)
    (sixLabelled_plusWitness_neutral_entry_zero label D) j k hj hk

/-- At 01↔10 saturation, the full corner parts of neutral
00,11 columns similarly form an orthonormal family. -/
theorem sixLabelled_exactHamming_saturated12_neutral_isometry
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = 0)
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ))
    (j k : Fin 6)
    (hj : squareMinusNeutral (label j))
    (hk : squareMinusNeutral (label k)) :
    (∑ i : Fin 6,
      if ¬squareMinusNeutral (label i) then
        star ((labelledSquareA label D - labelledSquareB label D) i j) *
          (labelledSquareA label D - labelledSquareB label D) i k
      else 0) = if j = k then (1 : ℂ) else 0 := by
  exact sixMatrix_involution_neutralColumns_orthonormal
    (labelledSquareA label D - labelledSquareB label D)
    (fun i => squareMinusNeutral (label i))
    (sixLabelled_exactHamming_saturated12_trueMatrixMinus_involution label D hD hham h03 h12)
    (sixLabelled_minusWitness_isHermitian label D hD)
    (sixLabelled_minusWitness_neutral_entry_zero label D) j k hj hk

end Neoplatonic.LTR
