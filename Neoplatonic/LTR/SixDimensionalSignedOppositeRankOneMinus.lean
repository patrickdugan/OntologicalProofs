import Neoplatonic.LTR.SixDimensionalOppositeDoubleRankOne
import Mathlib.Tactic

/-!
# LTR-MAN-95: genuine labelled saturated negative opposite Dirac block

This module specializes the six-dimensional bipartite rank-one theorem
to the exact common Dirac matrix used for the Hamming commutators.

The negative witness corner has precisely the two complementary
truth fibres 01 and 10. All internal same-atom commutator blocks
vanish, and the two oriented off-diagonal blocks are disjoint.
Under exact Hamming saturation, MAN-93 and MAN-94 give corner
tripotence and square-trace two. They force the surviving Dirac
opposite block to have rank one, even if both endpoint fibres
have multiplicity two.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The minus neutral complement is the sum of the orthogonal
01 and 10 truth-fibre projections, for every labelled chart. -/
theorem sixMinus_complement_eq_oppositeFibreProjections
    (label : Fin 6 → Fin 4) :
    (1 - sixTruthSectorProjection label squareMinusNeutral : SixMat) =
      sixTruthFibreProjection label 1 +
        sixTruthFibreProjection label 2 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    generalize hli : label i = u
    fin_cases u <;>
      simp [sixTruthSectorProjection, sixTruthFibreProjection,
        squareMinusNeutral, Matrix.sub_apply, Matrix.add_apply,
        Matrix.one_apply, Matrix.diagonal_apply, hli]
  · simp [sixTruthSectorProjection, sixTruthFibreProjection,
      Matrix.sub_apply, Matrix.add_apply,
      Matrix.one_apply, Matrix.diagonal_apply, hij]

/-- Distinct truth-atom projections have orthogonal products. -/
theorem sixOpposite12_fibreProjections_orthogonal
    (label : Fin 6 → Fin 4) :
    sixTruthFibreProjection label 1 *
        sixTruthFibreProjection label 2 = 0 ∧
      sixTruthFibreProjection label 2 *
        sixTruthFibreProjection label 1 = 0 := by
  constructor
  · ext i j
    simp only [sixTruthFibreProjection, Matrix.diagonal_mul]
    by_cases hi : label i = 1 <;> simp [hi, Matrix.diagonal_apply]
  · ext i j
    simp only [sixTruthFibreProjection, Matrix.diagonal_mul]
    by_cases hi : label i = 2 <;> simp [hi, Matrix.diagonal_apply]

/-- Same-truth-atom blocks of the genuine positive coordinate
commutator vanish, whatever the fibre multiplicity. -/
theorem sixLabelled_minusWitness_oppositeInternalBlocks_zero
    (label : Fin 6 → Fin 4) (D : SixMat) :
    let W := labelledSquareA label D - labelledSquareB label D
    sixTruthFibreBlock label W 1 1 = 0 ∧
      sixTruthFibreBlock label W 2 2 = 0 := by
  dsimp only
  constructor
  · ext i j
    rw [sixTruthFibreBlock_entry]
    by_cases hi : label i = 1 <;> by_cases hj : label j = 1 <;>
      simp [hi, hj, Matrix.add_apply, labelledSquareA, labelledSquareB,
        squareTruthBitP, squareTruthBitQ]
  · ext i j
    rw [sixTruthFibreBlock_entry]
    by_cases hi : label i = 2 <;> by_cases hj : label j = 2 <;>
      simp [hi, hj, Matrix.add_apply, labelledSquareA, labelledSquareB,
        squareTruthBitP, squareTruthBitQ]

/-- The actual 01-to-10 Dirac block is rank one at negative
saturation, including the opposite-double 2+2 pattern.
The result is independent of a choice of coordinate permutation. -/
theorem sixLabelled_exactHamming_saturated12_oppositeBlockRankOne
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = 0)
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    (sixTruthFibreBlock label D 1 2).rank = 1 := by
  let W : SixMat := labelledSquareA label D - labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squareMinusNeutral
  let P : SixMat := sixTruthFibreProjection label 1
  let R : SixMat := sixTruthFibreProjection label 2
  let X : SixMat := sixComplementCornerBlock W Q
  let B : SixMat := P * W * R
  let Z : SixMat := R * W * P
  have hW : W * W = 1 :=
    sixLabelled_exactHamming_saturated12_trueMatrixMinus_involution
      label D hD hham h03 h12
  have hQ2 : Q * Q = Q :=
    sixTruthSectorProjection_idempotent label squareMinusNeutral
  have hQQ : Q * W * Q = 0 :=
    sixTruthSectorProjection_W_zero label squareMinusNeutral W
      (sixLabelled_minusWitness_neutral_entry_zero label D)
  have hP2 : P * P = P := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label
        (fun u : Fin 4 => u = 1))
  have hR2 : R * R = R := by
    simpa only [R, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label
        (fun u : Fin 4 => u = 2))
  obtain ⟨hPR, hRP⟩ :=
    sixOpposite12_fibreProjections_orthogonal label
  have hC : (1 - Q : SixMat) = P + R :=
    sixMinus_complement_eq_oppositeFibreProjections label
  obtain ⟨hPWP, hRWR⟩ :=
    sixLabelled_minusWitness_oppositeInternalBlocks_zero label D
  change P * W * P = 0 at hPWP
  change R * W * R = 0 at hRWR
  have hX : X = B + Z := by
    change (1 - Q) * W * (1 - Q) = B + Z
    rw [hC]
    change (P + R) * W * (P + R) =
      P * W * R + R * W * P
    calc
      (P + R) * W * (P + R) =
          P * W * P + P * W * R + R * W * P + R * W * R := by
            noncomm_ring
      _ = P * W * R + R * W * P := by
        rw [hPWP, hRWR]
        simp
  have hBB : B * B = 0 := by
    change (P * W * R) * (P * W * R) = 0
    calc
      _ = P * W * (R * P) * W * R := by noncomm_ring
      _ = 0 := by rw [hRP]; simp
  have hZZ : Z * Z = 0 := by
    change (R * W * P) * (R * W * P) = 0
    calc
      _ = R * W * (P * R) * W * P := by noncomm_ring
      _ = 0 := by rw [hPR]; simp
  have hPB : P * B = B := by
    change P * (P * W * R) = P * W * R
    calc
      _ = (P * P) * W * R := by noncomm_ring
      _ = P * W * R := by rw [hP2]
  have hBR : B * R = B := by
    change (P * W * R) * R = P * W * R
    calc
      _ = P * W * (R * R) := by noncomm_ring
      _ = P * W * R := by rw [hR2]
  have hPZ : P * Z = 0 := by
    change P * (R * W * P) = 0
    calc
      _ = (P * R) * W * P := by noncomm_ring
      _ = 0 := by rw [hPR]; simp
  have hZR : Z * R = 0 := by
    change (R * W * P) * R = 0
    calc
      _ = R * W * (P * R) := by noncomm_ring
      _ = 0 := by rw [hPR]; simp
  have hX3 : X * X * X = X :=
    sixMatrix_involution_zeroNeutral_corner_tripotent
      W Q hW hQ2 hQQ
  have hX2rank : (X * X).rank = 2 := by
    have h := (sixLabelled_exactHamming_saturated12_cornerRankTwo
      label D hD hham h03 h12).2
    change (X * X).rank = 2 at h
    exact h
  have hX2id := sixMatrix_tripotent_square_idempotent X hX3
  have hXtrace : (X * X).trace = (2 : ℂ) := by
    have h := sixMatrix_idempotent_trace_eq_rank (X * X) hX2id
    rw [hX2rank] at h
    exact h
  have htripBZ :
      (B + Z) * (B + Z) * (B + Z) = B + Z := by
    rw [← hX]
    exact hX3
  have htraceBZ :
      ((B + Z) * (B + Z)).trace = (2 : ℂ) := by
    rw [← hX]
    exact hXtrace
  have hBrank : B.rank = 1 :=
    sixMatrix_bipartite_tripotent_traceTwo_rankOne
      B Z P R hBB hZZ hPB hBR hPZ hZR htripBZ htraceBZ
  have hBscalar :
      B = ((-2 : ℂ) * Complex.I) •
        sixTruthFibreBlock label D 1 2 := by
    change sixTruthFibreBlock label
      (labelledSquareA label D - labelledSquareB label D) 1 2 = _
    apply sixTruthFibreBlock_smul_of_entries
    intro i j hi hj
    simp [Matrix.sub_apply, labelledSquareA, labelledSquareB,
      squareTruthBitP, squareTruthBitQ, hi, hj] <;> ring
  have hScaleRank : B.rank =
      (sixTruthFibreBlock label D 1 2).rank := by
    rw [hBscalar]
    exact Matrix.rank_smul_of_mem_nonZeroDivisors
      (sixTruthFibreBlock label D 1 2)
      (mem_nonZeroDivisors_of_ne_zero
        (by norm_num : ((-2 : ℂ) * Complex.I) ≠ 0))
  exact hScaleRank.symm.trans hBrank

end Neoplatonic.LTR
