import Neoplatonic.LTR.SixDimensionalNearHalfTraceRigidity
import Neoplatonic.LTR.SixDimensionalNearHalfTransitionGramBudget
import Neoplatonic.LTR.SixDimensionalUniformHalfCornerBound
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-172: one-sided spectral defect and fibre trace positivity

For any contraction W in the original complex 6×6 Euclidean Hilbert
operator norm, Δ=I-W² has nonnegative REAL diagonal, since
  Re (W²)ᵢᵢ ≤ |(W²)ᵢᵢ| ≤ ||W²|| ≤ ||W||² ≤ 1.
Hermiticity is not required for this diagonal inequality.

Consequently every original truth-fibre compression has
  Re Tr(Pu Δ Pu) ≥ 0.
The signed trace defect of MAN-161 also enjoys a one-sided bound:
  Re ∑ᵢ sᵢ Δᵢᵢ ≥ -|neutral| * ||Δ||,
where sᵢ=-1 on neutral indices and +1 on the complement.

These results sharpen the transition-row and opposite-energy
bounds used in MAN-162/165 without invoking spectral saturation,
residual rank assumptions, or a canonical eigenbasis.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Every diagonal entry of I-W² has nonnegative real part
whenever W is a Euclidean Hilbert operator contraction. -/
theorem sixMatrix_contraction_squareDefect_diagonal_re_nonneg
    (W : SixMat) (hW : ‖W‖ ≤ (1 : ℝ)) (i : Fin 6) :
    0 ≤ (((1 : SixMat) - W * W) i i).re := by
  have hSq : ‖W * W‖ ≤ (1 : ℝ) := by
    calc
      ‖W * W‖ ≤ ‖W‖ * ‖W‖ := Matrix.l2_opNorm_mul W W
      _ ≤ 1 := by nlinarith [norm_nonneg W]
  have hEntry : ‖(W * W) i i‖ ≤ ‖W * W‖ := by
    rw [Matrix.cstar_norm_def]
    change ‖(W * W) i i‖ ≤
      ‖(W * W).toEuclideanLin.toContinuousLinearMap‖
    exact sixMatrix_entryNorm_le_operatorNorm (W * W) i i
  have hReal : ((W * W) i i).re ≤ ‖(W * W) i i‖ :=
    Complex.re_le_norm _
  have hDiag :
      (((1 : SixMat) - W * W) i i).re =
        1 - ((W * W) i i).re := by
    simp [Matrix.sub_apply, Matrix.one_apply]
  rw [hDiag]
  linarith

/-- A diagonal truth-fibre projection compresses only diagonal
entries in its support; each defect diagonal is nonnegative. -/
theorem sixTruthFibre_contraction_squareDefect_trace_re_nonneg
    (label : Fin 6 → Fin 4) (W : SixMat)
    (hW : ‖W‖ ≤ (1 : ℝ)) (u : Fin 4) :
    0 ≤ ((sixTruthFibreProjection label u *
        ((1 : SixMat) - W * W) *
          sixTruthFibreProjection label u).trace).re := by
  let P : SixMat := sixTruthFibreProjection label u
  let Δ : SixMat := 1 - W * W
  have hPid : P * P = P := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection]
      using sixTruthSectorProjection_idempotent
        label (fun t : Fin 4 => t = u)
  have hTrace : (P * Δ * P).trace =
      ∑ i : Fin 6, if label i = u then Δ i i else 0 := by
    rw [sixMatrix_trace_doubleCompression_eq_leftCompression P Δ hPid]
    simp [P, sixTruthFibreProjection, Matrix.trace,
      Matrix.diag, Matrix.diagonal_mul]
  change 0 ≤ (P * Δ * P).trace.re
  rw [hTrace]
  have hRe :
      (∑ i : Fin 6, if label i = u then Δ i i else 0).re =
        ∑ i : Fin 6, if label i = u then (Δ i i).re else 0 := by
    simp [Complex.re_sum]
  rw [hRe]
  apply Finset.sum_nonneg
  intro i hi
  by_cases hui : label i = u
  · simp only [hui, ite_true]
    change 0 ≤ (((1 : SixMat) - W * W) i i).re
    exact sixMatrix_contraction_squareDefect_diagonal_re_nonneg W hW i
  · simp [hui]

/-- For nonnegative real diagonal entries, the signed trace sum
is bounded BELOW by the mass of the neutral coordinates alone.
The complement contributes with a positive sign. -/
theorem sixMatrix_signedDiagonal_re_lower_of_nonneg
    (M : SixMat) (neutral : Fin 6 → Prop) [DecidablePred neutral]
    (hdiag : ∀ i : Fin 6, 0 ≤ (M i i).re) :
    -((Finset.univ.filter neutral).card : ℝ) * ‖M‖ ≤
      (∑ i : Fin 6,
        if neutral i then -(M i i) else M i i).re := by
  have hEntry (i : Fin 6) : ‖M i i‖ ≤ ‖M‖ := by
    rw [Matrix.cstar_norm_def]
    change ‖M i i‖ ≤ ‖M.toEuclideanLin.toContinuousLinearMap‖
    exact sixMatrix_entryNorm_le_operatorNorm M i i
  have hPoint (i : Fin 6) :
      -(if neutral i then ‖M‖ else 0) ≤
      (if neutral i then -(M i i).re else (M i i).re) := by
    by_cases hn : neutral i
    · simp only [hn, if_true]
      have h := Complex.re_le_norm (M i i)
      linarith [hEntry i]
    · simpa [hn] using hdiag i
  have hSum : (∑ i : Fin 6,
      -(if neutral i then ‖M‖ else 0)) ≤
      (∑ i : Fin 6,
        if neutral i then -(M i i).re else (M i i).re) :=
    Finset.sum_le_sum (fun i _ => hPoint i)
  have hLeft :
      (∑ i : Fin 6, -(if neutral i then ‖M‖ else 0)) =
      -((Finset.univ.filter neutral).card : ℝ) * ‖M‖ := by
    rw [Finset.sum_neg_distrib]
    rw [← Finset.sum_filter]
    simp [nsmul_eq_mul]
  have hRight :
      (∑ i : Fin 6,
        if neutral i then -(M i i).re else (M i i).re) =
      (∑ i : Fin 6,
        if neutral i then -(M i i) else M i i).re := by
    simp [Complex.re_sum]
  rw [← hLeft, ← hRight]
  exact hSum

/-- The actual positive signed Hamming witness inherits
nonnegative real defect traces on all four truth-atom fibres. -/
theorem sixLabelled_exactHamming_plusDefect_fibreTrace_re_nonneg
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (u : Fin 4) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Δ : SixMat := 1 - W * W
    0 ≤ ((sixTruthFibreProjection label u * Δ *
      sixTruthFibreProjection label u).trace).re := by
  dsimp only
  exact sixTruthFibre_contraction_squareDefect_trace_re_nonneg
    label (labelledSquareA label D + labelledSquareB label D)
      (sixLabelled_exactHamming_plusWitness_norm_le_one label D hD hham) u

end Neoplatonic.LTR
