import Neoplatonic.LTR.SixDimensionalSignedOppositeMinors
import Neoplatonic.LTR.SixDimensionalOppositeBlockTraceIdentity
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# LTR-MAN-95: exact quarter-energy Gram polynomial for saturated opposite blocks

The true saturated Dirac opposite block has rank one. In complex
Hilbert coordinates the trace of B Bᴴ is precisely the sum of
the squared entry norms. Rank-one minors imply

    B Bᴴ B = Tr(B Bᴴ) B.

At the saturated energy 1/4 this makes 4 B Bᴴ a rank-one
idempotent with trace one. The spectrum of B Bᴴ lies in
{0, 1/4}, and its unique nonzero singular value is 1/2.

This file gives exact matrix equations in the original Fin 6
coordinates, avoiding any choice of singular vectors or basis.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A finite complex matrix's Gram trace is its squared
Frobenius norm, expressed as a sum of entrywise squared moduli. -/
theorem sixMatrix_gram_trace_eq_entryEnergy (B : SixMat) :
    (B * B.conjTranspose).trace =
      ((∑ j : Fin 6, ∑ i : Fin 6, ‖B i j‖ ^ 2 : ℝ) : ℂ) := by
  have htr : (B * B.conjTranspose).trace =
      ∑ i : Fin 6, ∑ j : Fin 6, B i j * star (B i j) := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
  rw [htr, Finset.sum_comm]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro i hi
  simpa only [map_pow] using
    (complex_cast_norm_sq_eq_mul_star (B i j)).symm

/-- The square of the true truth-fibre block, traced on the
output fibre, is the oriented squared coupling energy. -/
theorem sixTruthFibreBlock_gram_trace_eq_energy
    (label : Fin 6 → Fin 4) (D : SixMat) (u v : Fin 4) :
    ((sixTruthFibreBlock label D u v) *
       (sixTruthFibreBlock label D u v).conjTranspose).trace =
      ((sixTruthFibreBlockEnergy label D u v : ℝ) : ℂ) := by
  simpa only [sixTruthFibreBlockEnergy] using
    sixMatrix_gram_trace_eq_entryEnergy
      (sixTruthFibreBlock label D u v)

/-- The universal cubic Gram identity for a rank-one complex
six-dimensional matrix. Its proof uses exactly the vanishing
2x2 minors and finite matrix multiplication. -/
theorem sixMatrix_rankOne_gram_cubic
    (B : SixMat) (hRank : B.rank = 1) :
    (B * B.conjTranspose) * B =
      (B * B.conjTranspose).trace • B := by
  have hminor := sixMatrix_rankOne_allTwoByTwoMinors_zero B hRank
  have htr : (B * B.conjTranspose).trace =
      ∑ k : Fin 6, ∑ l : Fin 6,
        B k l * star (B k l) := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
  ext i j
  rw [Matrix.mul_apply, Matrix.smul_apply, htr]
  calc
    (∑ k : Fin 6, (B * B.conjTranspose) i k * B k j) =
      ∑ k : Fin 6, ∑ l : Fin 6,
        (B i l * B k j) * star (B k l) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Matrix.mul_apply, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro l hl
          rw [Matrix.conjTranspose_apply]
          ring
    _ = ∑ k : Fin 6, ∑ l : Fin 6,
          (B i j * B k l) * star (B k l) := by
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          rw [← hminor i k j l]
    _ = (∑ k : Fin 6, ∑ l : Fin 6,
          B k l * star (B k l)) * B i j := by
          simp only [Finset.sum_mul, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          apply Finset.sum_congr rfl
          intro l hl
          ring

/-- If a rank-one complex matrix has Gram trace one quarter,
its scaled Gram matrix is exactly an idempotent of trace one.
This characterizes the sole nonzero singular value as 1/2. -/
theorem sixMatrix_rankOne_quarterGram_projection
    (B : SixMat)
    (hRank : B.rank = 1)
    (htrace : (B * B.conjTranspose).trace = (1 / 4 : ℂ)) :
    (((4 : ℂ) • (B * B.conjTranspose)) *
      ((4 : ℂ) • (B * B.conjTranspose)) =
        ((4 : ℂ) • (B * B.conjTranspose))) ∧
      (((4 : ℂ) • (B * B.conjTranspose)).trace = 1) := by
  let H : SixMat := B * B.conjTranspose
  have hCube : H * B = (1 / 4 : ℂ) • B := by
    have h := sixMatrix_rankOne_gram_cubic B hRank
    change H * B = H.trace • B at h
    rw [htrace] at h
    exact h
  have hHH : H * H = (1 / 4 : ℂ) • H := by
    calc
      H * H = (H * B) * B.conjTranspose := by
        dsimp [H]; noncomm_ring
      _ = ((1 / 4 : ℂ) • B) * B.conjTranspose := by rw [hCube]
      _ = (1 / 4 : ℂ) • H := by
        rw [Matrix.smul_mul]
  constructor
  · change ((4 : ℂ) • H) * ((4 : ℂ) • H) = (4 : ℂ) • H
    rw [Matrix.smul_mul, Matrix.mul_smul, hHH]
    simp [smul_smul]
  · change ((4 : ℂ) • H).trace = 1
    rw [Matrix.trace_smul, htrace]
    norm_num

/-- The 00/11 saturated original Dirac coupling has a
quarter-unit Gram projection, in the actual Fin 6 coordinates. -/
theorem sixLabelled_exactHamming_saturated03_oppositeBlock_quarterGram
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    let B := sixTruthFibreBlock label D 0 3
    (((4 : ℂ) • (B * B.conjTranspose)) *
      ((4 : ℂ) • (B * B.conjTranspose)) =
        ((4 : ℂ) • (B * B.conjTranspose))) ∧
      (((4 : ℂ) • (B * B.conjTranspose)).trace = 1) := by
  dsimp only
  apply sixMatrix_rankOne_quarterGram_projection
  · exact sixLabelled_exactHamming_saturated03_oppositeBlockRankOne
      label D hD hham h03 h12
  · rw [sixTruthFibreBlock_gram_trace_eq_energy, h03]
    norm_num

/-- The 01/10 saturated original Dirac coupling satisfies
the same exact quarter-unit Gram equations. -/
theorem sixLabelled_exactHamming_saturated12_oppositeBlock_quarterGram
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = 0)
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    let B := sixTruthFibreBlock label D 1 2
    (((4 : ℂ) • (B * B.conjTranspose)) *
      ((4 : ℂ) • (B * B.conjTranspose)) =
        ((4 : ℂ) • (B * B.conjTranspose))) ∧
      (((4 : ℂ) • (B * B.conjTranspose)).trace = 1) := by
  dsimp only
  apply sixMatrix_rankOne_quarterGram_projection
  · exact sixLabelled_exactHamming_saturated12_oppositeBlockRankOne
      label D hD hham h03 h12
  · rw [sixTruthFibreBlock_gram_trace_eq_energy, h12]
    norm_num

end Neoplatonic.LTR
