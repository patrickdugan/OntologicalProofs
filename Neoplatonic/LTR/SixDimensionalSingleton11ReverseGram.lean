import Neoplatonic.LTR.SixDimensionalSingletonOppositeExhaustion
import Neoplatonic.LTR.SixDimensionalSignedOppositeRankOne
import Neoplatonic.LTR.SixDimensionalSignedOppositeGram
import Mathlib.Tactic

/-!
# LTR-MAN-110: input-side Gram projector exhausts a singleton 11 fibre

MAN-96 proves the saturated rank-one Gram projection of the
true 00-to-11 Dirac block. Its rank-one cubic identity gives the
same quarter-unit projector for the reversed Gram BᴴB, directly
in the original six-dimensional basis.

When the input 11 truth fibre is a singleton, its projector
equals 4BᴴB. This supplies the input-side analogue of MAN-105
without relying on any extra matrix-rank API for complex
conjugate transposes.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- For a rank-one complex six-dimensional matrix of quarter
Gram trace, the reversed Gram has a trace-one scaled
idempotent as well. -/
theorem sixMatrix_rankOne_quarterReverseGram_projection
    (B : SixMat)
    (hRank : B.rank = 1)
    (hTrace : (B * B.conjTranspose).trace = (1 / 4 : ℂ)) :
    let H : SixMat := (4 : ℂ) • (B.conjTranspose * B)
    H * H = H ∧ H.trace = (1 : ℂ) := by
  dsimp only
  have hCubic := sixMatrix_rankOne_gram_cubic B hRank
  have hQuarter : (B * B.conjTranspose) * B =
      (1 / 4 : ℂ) • B := by
    rw [hCubic, hTrace]
  have hRevSq :
      (B.conjTranspose * B) * (B.conjTranspose * B) =
        (1 / 4 : ℂ) • (B.conjTranspose * B) := by
    calc
      (B.conjTranspose * B) * (B.conjTranspose * B) =
          B.conjTranspose * ((B * B.conjTranspose) * B) := by
            noncomm_ring
      _ = B.conjTranspose * ((1 / 4 : ℂ) • B) := by rw [hQuarter]
      _ = (1 / 4 : ℂ) • (B.conjTranspose * B) := by
        rw [Matrix.mul_smul]
  have hRevTrace :
      (B.conjTranspose * B).trace = (1 / 4 : ℂ) := by
    rw [Matrix.trace_mul_comm, hTrace]
  constructor
  · rw [Matrix.smul_mul, Matrix.mul_smul, hRevSq]
    simp [smul_smul]
  · rw [Matrix.trace_smul, hRevTrace]
    norm_num

/-- At positive saturation, the actual singleton 11 truth
fibre is fully occupied by the input-side Dirac Gram. -/
theorem sixLabelled_exactHamming_saturated03_singleton11_finalGram
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (hMult : truthMultiplicity label 3 = 1) :
    let B := sixTruthFibreBlock label D 0 3
    sixTruthFibreProjection label 3 =
      (4 : ℂ) • (B.conjTranspose * B) := by
  dsimp only
  let B : SixMat := sixTruthFibreBlock label D 0 3
  have hRank : B.rank = 1 :=
    sixLabelled_exactHamming_saturated03_oppositeBlockRankOne
      label D hD hham h03 h12
  have hTrace : (B * B.conjTranspose).trace = (1 / 4 : ℂ) := by
    rw [sixTruthFibreBlock_gram_trace_eq_energy, h03]
    norm_num
  have hRev := sixMatrix_rankOne_quarterReverseGram_projection
    B hRank hTrace
  change ((4 : ℂ) • (B.conjTranspose * B)) *
      ((4 : ℂ) • (B.conjTranspose * B)) =
        (4 : ℂ) • (B.conjTranspose * B) ∧
      ((4 : ℂ) • (B.conjTranspose * B)).trace = 1 at hRev
  have hB30 : B.conjTranspose =
      sixTruthFibreBlock label D 3 0 :=
    sixTruthFibreBlock_conjTranspose label D hD 0 3
  have hGram30 :
      let B30 := sixTruthFibreBlock label D 3 0
      let H : SixMat := (4 : ℂ) • (B30 * B30.conjTranspose)
      H * H = H ∧ H.trace = (1 : ℂ) := by
    dsimp only
    rw [← hB30, Matrix.conjTranspose_conjTranspose]
    exact hRev
  have hFilled :=
    sixTruthFibreBlock_singleton_finalGram_eq_fibre
      label D 3 0 hMult hGram30
  change sixTruthFibreProjection label 3 =
      (4 : ℂ) •
        ((sixTruthFibreBlock label D 3 0) *
          (sixTruthFibreBlock label D 3 0).conjTranspose) at hFilled
  rw [← hB30, Matrix.conjTranspose_conjTranspose] at hFilled
  exact hFilled

end Neoplatonic.LTR
