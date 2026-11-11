import Neoplatonic.LTR.SixDimensionalSingletonOppositeExhaustion
import Neoplatonic.LTR.SixDimensionalSingletonNeutralRowExtinction
import Mathlib.Analysis.Complex.Order
import Mathlib.Tactic

/-!
# LTR-MAN-110: reverse orientation saturated Gram exhausts singleton 11

The 00-to-11 Dirac block from MAN-95 is rank one, even when both
truth fibres have multiplicity two. Hermitianity identifies the
reverse 11-to-00 block with its conjugate transpose. This reverses
the Gram trace and rank exactly.

At positive saturation the 11-to-00 block also has Gram trace
one-quarter. Its fourfold Gram is therefore an idempotent of trace
one, as in MAN-96. If the 11 fibre has multiplicity one, MAN-105's
nested-projection theorem gives P11=4D30 D30ᴴ.

The point is to obtain the *reverse* singleton projector needed
for the mirrored triple-fibre obstruction.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal ComplexOrder

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Positive saturation forces the true reverse opposite block to
have rank one in its original six-dimensional coordinates. -/
theorem sixLabelled_exactHamming_saturated03_reverseBlockRankOne
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    (sixTruthFibreBlock label D 3 0).rank = 1 := by
  have hRank :=
    sixLabelled_exactHamming_saturated03_oppositeBlockRankOne
      label D hD hham h03 h12
  rw [← sixTruthFibreBlock_conjTranspose label D hD 0 3]
  simpa only [Matrix.rank_conjTranspose] using hRank

/-- Reverse 11-to-00 block inherits the exact quarter-Gram
projection certificate from Hermitianity and MAN-96. -/
theorem sixLabelled_exactHamming_saturated03_reverseBlock_quarterGram
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    let B := sixTruthFibreBlock label D 3 0
    let H : SixMat := (4 : ℂ) • (B * B.conjTranspose)
    H * H = H ∧ H.trace = (1 : ℂ) := by
  dsimp only
  apply sixMatrix_rankOne_quarterGram_projection
    (sixTruthFibreBlock label D 3 0)
  · exact sixLabelled_exactHamming_saturated03_reverseBlockRankOne
      label D hD hham h03 h12
  · rw [sixTruthFibreBlock_gram_trace_eq_energy]
    rw [← sixTruthFibreBlockEnergy_reverse label D hD 0 3, h03]
    norm_num

/-- A singleton 11 truth atom is exhausted by the *reverse*
oriented 11-to-00 Dirac Gram projector. -/
theorem sixLabelled_exactHamming_saturated03_singleton11_finalGram
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (hMult : truthMultiplicity label 3 = 1) :
    sixTruthFibreProjection label 3 =
      (4 : ℂ) •
        ((sixTruthFibreBlock label D 3 0) *
          (sixTruthFibreBlock label D 3 0).conjTranspose) := by
  exact sixTruthFibreBlock_singleton_finalGram_eq_fibre
    label D 3 0 hMult
    (sixLabelled_exactHamming_saturated03_reverseBlock_quarterGram
      label D hD hham h03 h12)

/-- The saturated reverse Dirac Gram occupies a singleton 11 truth
fibre; its 11-to-neutral exchange must therefore vanish. -/
theorem sixLabelled_exactHamming_saturated03_singleton11_neutralRow_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (hMult : truthMultiplicity label 3 = 1) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    let R := sixTruthFibreProjection label 3
    let Y := C * W * Q
    R * Y = 0 := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let R : SixMat := sixTruthFibreProjection label 3
  let Y : SixMat := C * W * Q
  let B : SixMat := sixTruthFibreBlock label D 3 0
  let T : SixMat := ((2 : ℂ) * Complex.I) •
    sixTruthFibreBlock label D 0 3
  change R * Y = 0
  have hRH : R.IsHermitian := by
    simpa only [R, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label (fun u : Fin 4 => u = 3))
  have hFibre :=
    (sixLabelled_exactHamming_saturated03_fibreNeutralGram
      label D hD hham h03 h12).2
  change R * (Y * Y.conjTranspose) * R =
    R - T.conjTranspose * T at hFibre
  have hFull :=
    sixLabelled_exactHamming_saturated03_singleton11_finalGram
      label D hD hham h03 h12 hMult
  change R = (4 : ℂ) • (B * B.conjTranspose) at hFull
  have hBack : (sixTruthFibreBlock label D 0 3).conjTranspose = B :=
    sixTruthFibreBlock_conjTranspose label D hD 0 3
  have hTGram : T.conjTranspose * T =
      (4 : ℂ) • (B * B.conjTranspose) := by
    dsimp [T]
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul, hBack]
    have hc : star ((2 : ℂ) * Complex.I) *
        ((2 : ℂ) * Complex.I) = 4 := by
      norm_num [Complex.I_mul_I]
    rw [hc]
  have hGram : R * (Y * Y.conjTranspose) * R = 0 := by
    rw [hTGram, ← hFull] at hFibre
    simpa using hFibre
  exact sixMatrix_hermitianGramCompression_zero_forces_zero
    R Y hRH hGram

end Neoplatonic.LTR
