import Neoplatonic.LTR.SixDimensionalSignedNeutralExchangeDefect
import Neoplatonic.LTR.SixDimensionalOppositeFibreProjectionDefect
import Neoplatonic.LTR.SixDimensionalSingleton11NeutralRowExtinction
import Neoplatonic.LTR.SixDimensionalSaturated03Singleton00NoGo
import Mathlib.Tactic

/-!
# LTR-MAN-113: the two rank-one defect channels in the true 2+2 Hamming corner

MAN-109 and MAN-112 exclude pure positive 00/11 saturation with
a singleton opposite endpoint. Hence the only surviving faithful
six-dimensional positive saturation candidate has fibre sizes
(2,1,1,2). The surviving original Dirac block B = D03 has rank
one and singular value 1/2 (MAN-95/96).

The neutral exchange Y = C (A+B) Q satisfies the exact identity

    Y Yᴴ = (P0 - 4 B Bᴴ) + (P3 - 4 Bᴴ B).

Both summands are idempotents of rank one on separate doubled truth
fibres. The reverse Gram certificate comes from MAN-110 and the
general doubled-fibre defect theorem from MAN-103.

This gives an original-coordinate decomposition into two canonical
one-dimensional output channels without selecting a singular-vector
basis or postulating the final U(2) chart.

The subsequent operator-norm identification remains a separate
obligation before asserting the full exact-Hamming no-go.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal ComplexOrder
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- An exact four-sector Gram balance yields the decomposition
of the neutral exchange into the local defects of the opposite
Dirac channel. -/
theorem sixMatrix_neutralGram_eq_sum_oppositeDefects
    (P R Y T : SixMat)
    (h : Y * Y.conjTranspose +
      T * T.conjTranspose + T.conjTranspose * T = P + R) :
    Y * Y.conjTranspose =
      (P - T * T.conjTranspose) +
        (R - T.conjTranspose * T) := by
  calc
    Y * Y.conjTranspose =
        (Y * Y.conjTranspose +
          T * T.conjTranspose + T.conjTranspose * T) -
          T * T.conjTranspose - T.conjTranspose * T := by abel
    _ = (P + R) - T * T.conjTranspose -
          T.conjTranspose * T := by rw [h]
    _ = (P - T * T.conjTranspose) +
          (R - T.conjTranspose * T) := by abel

/-- In the actual six-dimensional labelled Dirac representation,
the positive-saturated neutral exchange is the direct sum of the
two exact oriented Gram defects of the surviving 00/11 block. -/
theorem sixLabelled_exactHamming_saturated03_neutralGram_twoDefects
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    let Y := C * W * Q
    let B := sixTruthFibreBlock label D 0 3
    let P0 := sixTruthFibreProjection label 0
    let P3 := sixTruthFibreProjection label 3
    Y * Y.conjTranspose =
      (P0 - (4 : ℂ) • (B * B.conjTranspose)) +
        (P3 - (4 : ℂ) • (B.conjTranspose * B)) := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let Y : SixMat := C * W * Q
  let B : SixMat := sixTruthFibreBlock label D 0 3
  let T : SixMat := ((2 : ℂ) * Complex.I) • B
  let P0 : SixMat := sixTruthFibreProjection label 0
  let P3 : SixMat := sixTruthFibreProjection label 3
  change Y * Y.conjTranspose =
    (P0 - (4 : ℂ) • (B * B.conjTranspose)) +
      (P3 - (4 : ℂ) • (B.conjTranspose * B))
  have hdef :=
    sixLabelled_exactHamming_saturated03_neutralExchange_defect
      label D hD hham h03 h12
  change Y * Y.conjTranspose + T * T.conjTranspose +
    T.conjTranspose * T = C at hdef
  have hC : C = P0 + P3 :=
    sixPlus_complement_eq_oppositeFibreProjections label
  rw [hC] at hdef
  have hT : T * T.conjTranspose =
      (4 : ℂ) • (B * B.conjTranspose) :=
    sixMatrix_positiveDoubleImagGram B
  have hTrev : T.conjTranspose * T =
      (4 : ℂ) • (B.conjTranspose * B) :=
    sixMatrix_positiveDoubleImagReverseGram B
  have hSum :=
    sixMatrix_neutralGram_eq_sum_oppositeDefects
      P0 P3 Y T hdef
  simpa only [hT, hTrev] using hSum

/-- In the doubled-output 00 fibre, the positive saturated
Dirac Gram leaves precisely one rank-one defect channel. -/
theorem sixLabelled_exactHamming_saturated03_double00_defect
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (hm0 : truthMultiplicity label 0 = 2) :
    let B := sixTruthFibreBlock label D 0 3
    let E0 := sixTruthFibreProjection label 0 -
      (4 : ℂ) • (B * B.conjTranspose)
    E0 * E0 = E0 ∧ E0.rank = 1 := by
  simpa only using
    (sixLabelled_exactHamming_saturated03_double00_gramDefectRankOne
      label D hD hham h03 h12 hm0)

/-- The mirrored 11 fibre has the same rank-one Gram defect.
Hermitian reversal identifies its final Gram with Bᴴ B. -/
theorem sixLabelled_exactHamming_saturated03_double11_defect
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (hm3 : truthMultiplicity label 3 = 2) :
    let B := sixTruthFibreBlock label D 0 3
    let E3 := sixTruthFibreProjection label 3 -
      (4 : ℂ) • (B.conjTranspose * B)
    E3 * E3 = E3 ∧ E3.rank = 1 := by
  dsimp only
  let B : SixMat := sixTruthFibreBlock label D 0 3
  let R : SixMat := sixTruthFibreProjection label 3
  let Brev : SixMat := sixTruthFibreBlock label D 3 0
  change (R - (4 : ℂ) • (B.conjTranspose * B)) *
      (R - (4 : ℂ) • (B.conjTranspose * B)) =
        R - (4 : ℂ) • (B.conjTranspose * B) ∧
      (R - (4 : ℂ) • (B.conjTranspose * B)).rank = 1
  have h :=
    sixTruthFibreBlock_doubleFibre_gramDefectRankOne
      label D 3 0 hm3
      (sixLabelled_exactHamming_saturated03_reverseBlock_quarterGram
        label D hD hham h03 h12)
  change (R - (4 : ℂ) • (Brev * Brev.conjTranspose)) *
      (R - (4 : ℂ) • (Brev * Brev.conjTranspose)) =
        R - (4 : ℂ) • (Brev * Brev.conjTranspose) ∧
      (R - (4 : ℂ) • (Brev * Brev.conjTranspose)).rank = 1 at h
  have hrev : B.conjTranspose = Brev :=
    sixTruthFibreBlock_conjTranspose label D hD 0 3
  rw [← hrev, Matrix.conjTranspose_conjTranspose] at h
  exact h

/-- The neutral-exchange Gram has exactly two separately
rank-one, fibre-supported channels in the only surviving pure
positive-saturation six-dimensional multiplicity pattern. -/
theorem sixLabelled_exactHamming_saturated03_oppositeDouble_twoRankOneChannels
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (hm0 : truthMultiplicity label 0 = 2)
    (hm3 : truthMultiplicity label 3 = 2) :
    let B := sixTruthFibreBlock label D 0 3
    let P0 := sixTruthFibreProjection label 0
    let P3 := sixTruthFibreProjection label 3
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    let Y := C * W * Q
    let E0 := P0 - (4 : ℂ) • (B * B.conjTranspose)
    let E3 := P3 - (4 : ℂ) • (B.conjTranspose * B)
    E0 * E0 = E0 ∧ E0.rank = 1 ∧
      E3 * E3 = E3 ∧ E3.rank = 1 ∧
      Y * Y.conjTranspose = E0 + E3 := by
  dsimp only
  obtain ⟨hE0, hr0⟩ :=
    sixLabelled_exactHamming_saturated03_double00_defect
      label D hD hham h03 h12 hm0
  obtain ⟨hE3, hr3⟩ :=
    sixLabelled_exactHamming_saturated03_double11_defect
      label D hD hham h03 h12 hm3
  have hY :=
    sixLabelled_exactHamming_saturated03_neutralGram_twoDefects
      label D hD hham h03 h12
  exact ⟨hE0, hr0, hE3, hr3, hY⟩

end Neoplatonic.LTR
