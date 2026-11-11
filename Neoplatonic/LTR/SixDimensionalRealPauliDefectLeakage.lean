import Neoplatonic.LTR.SixDimensionalAmbientPauliDefectNorm
import Neoplatonic.LTR.SixDimensionalDefectCompressionNorm
import Neoplatonic.LTR.SixDimensionalNearSignedDefect
import Mathlib.Tactic

/-!
# LTR-MAN-147: original 6D real Pauli defect and quantitative leakage

MAN-146 shows that the ambient signed spectral defect in the
original labelled complex six-dimensional Dirac chart has norm
||I-W_+²|| = |1-mu|, where mu is the scalar Pauli residual square.

For Hermitian traceless residual Pauli matrices M,N, their scalar
quadratics are real. MAN-84 identifies the real mixed coefficient
c with the original opposite-block imbalance 2(E03-E12).
The signed Gram contraction q+r+|c|<=1 makes 1-(q+r+c)>=0.

Therefore:
  ||I-W_+²|| = 1-(q+r+c).

When c>=0 and c>=1/2-epsilon, MAN-142 proves that this defect
is at most 2 epsilon. MAN-143 then bounds the genuine original
corner-neutral leakage ||XY|| and neutral isometry defect by
2 epsilon. The interior nonsaturated case remains open.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ
private abbrev TwoMat := Matrix (Fin 2) (Fin 2) ℂ

/-- The norm of the FULL original signed six-dimensional Dirac
square defect equals the real Pauli scalar defect, exactly. -/
theorem sixLabelled_exactHamming_plusDefect_norm_eq_realPauli
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    ∃ S : TwoDirectionExtremalSystem SixH,
      ∃ hq : Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus),
      S.A = sixLabelledAOperator label D ∧
      S.B = sixLabelledBOperator label D ∧
      let W := labelledSquareA label D + labelledSquareB label D
      let M := S.sixDimResidualMatrixA hq (by simp)
      let N := S.sixDimResidualMatrixB hq (by simp)
      let q := pauliRealQuadratic M
      let r := pauliRealQuadratic N
      let c := sixOrientedOppositeEnergyImbalance label D
      ‖(1 : SixMat) - W * W‖ = 1 - (q + r + c) := by
  obtain ⟨S, hq, hA, hB, hNorm⟩ :=
    sixLabelled_exactHamming_plusDefect_norm_eq_pauliScalar
      label D hD hham
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let M : TwoMat := S.sixDimResidualMatrixA hq (by simp)
  let N : TwoMat := S.sixDimResidualMatrixB hq (by simp)
  let q : ℝ := pauliRealQuadratic M
  let r : ℝ := pauliRealQuadratic N
  let c : ℝ := sixOrientedOppositeEnergyImbalance label D
  change ‖(1 : SixMat) - W * W‖ =
    ‖(1 : ℂ) - (pauliQuadratic M +
      pauliQuadratic N + pauliMixed M N)‖ at hNorm
  have hMH : M.IsHermitian :=
    S.sixDimResidualMatrixA_isHermitian hq (by simp)
  have hNH : N.IsHermitian :=
    S.sixDimResidualMatrixB_isHermitian hq (by simp)
  have hMix : pauliMixed M N = (c : ℂ) := by
    exact sixLabelled_extremal_pauliMixed_eq_realImbalance
      label D hD S hq hA hB
  have hMu :
      pauliQuadratic M + pauliQuadratic N + pauliMixed M N =
        ((q + r + c : ℝ) : ℂ) := by
    rw [pauliQuadratic_eq_realQuadratic_of_hermitian M hMH,
      pauliQuadratic_eq_realQuadratic_of_hermitian N hNH, hMix]
    push_cast
    ring
  have hMixReal : pauliRealMixed M N = c := by
    change (pauliMixed M N).re = c
    rw [hMix]
    simp
  have htrA : LinearMap.trace ℂ SixH S.A.toLinearMap = 0 := by
    rw [hA]
    exact (sixLabelled_operatorTrace_zero label D).1
  have htrB : LinearMap.trace ℂ SixH S.B.toLinearMap = 0 := by
    rw [hB]
    exact (sixLabelled_operatorTrace_zero label D).2
  obtain ⟨hq0, hr0, hdet, hbudget⟩ :=
    S.sixDimResidual_realGram_cone hq (by simp) htrA htrB
  have hbudget' : q + r + |c| ≤ 1 := by
    change q + r + |pauliRealMixed M N| ≤ 1 at hbudget
    rwa [hMixReal] at hbudget
  have hNonneg : 0 ≤ 1 - (q + r + c) := by
    have hcle : c ≤ |c| := le_abs_self c
    linarith
  refine ⟨S, hq, hA, hB, ?_⟩
  change ‖(1 : SixMat) - W * W‖ = 1 - (q + r + c)
  calc
    ‖(1 : SixMat) - W * W‖ =
        ‖(1 : ℂ) - (pauliQuadratic M +
          pauliQuadratic N + pauliMixed M N)‖ := hNorm
    _ = ‖(1 : ℂ) - ((q + r + c : ℝ) : ℂ)‖ := by rw [hMu]
    _ = 1 - (q + r + c) := by
      have hval : (1 : ℂ) - ((q + r + c : ℝ) : ℂ) =
        ((1 - (q + r + c) : ℝ) : ℂ) := by push_cast; ring
      rw [hval, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hNonneg]

/-- Near the positive forbidden Pauli endpoint, the genuine
signed six-dimensional Dirac matrix has a small spectral defect. -/
theorem sixLabelled_exactHamming_positiveNearHalf_defect_norm_le
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (ε : ℝ)
    (hc : 0 ≤ sixOrientedOppositeEnergyImbalance label D)
    (hnear : (1 / 2 : ℝ) - ε ≤
      sixOrientedOppositeEnergyImbalance label D) :
    let W := labelledSquareA label D + labelledSquareB label D
    ‖(1 : SixMat) - W * W‖ ≤ 2 * ε := by
  obtain ⟨S, hq, hA, hB, hNorm⟩ :=
    sixLabelled_exactHamming_plusDefect_norm_eq_realPauli
      label D hD hham
  let M : TwoMat := S.sixDimResidualMatrixA hq (by simp)
  let N : TwoMat := S.sixDimResidualMatrixB hq (by simp)
  let q : ℝ := pauliRealQuadratic M
  let r : ℝ := pauliRealQuadratic N
  let c : ℝ := sixOrientedOppositeEnergyImbalance label D
  have htrA : LinearMap.trace ℂ SixH S.A.toLinearMap = 0 := by
    rw [hA]
    exact (sixLabelled_operatorTrace_zero label D).1
  have htrB : LinearMap.trace ℂ SixH S.B.toLinearMap = 0 := by
    rw [hB]
    exact (sixLabelled_operatorTrace_zero label D).2
  obtain ⟨hq0, hr0, hdet, hbudget⟩ :=
    S.sixDimResidual_realGram_cone hq (by simp) htrA htrB
  have hMix : pauliRealMixed M N = c := by
    change (pauliMixed M N).re = c
    rw [sixLabelled_extremal_pauliMixed_eq_realImbalance
      label D hD S hq hA hB]
    simp [c]
  have hcone : 0 ≤ q ∧ 0 ≤ r ∧
      c ^ 2 ≤ 4 * q * r ∧ q + r + |c| ≤ 1 := by
    change 0 ≤ q at hq0
    change 0 ≤ r at hr0
    change (pauliRealMixed M N) ^ 2 ≤ 4 * q * r at hdet
    change q + r + |pauliRealMixed M N| ≤ 1 at hbudget
    rw [hMix] at hdet hbudget
    exact ⟨hq0, hr0, hdet, hbudget⟩
  have hAbsNear : (1 / 2 : ℝ) - ε ≤ |c| := by
    rw [abs_of_nonneg hc]
    exact hnear
  have hGate := realGram_nearHalf_positive_signedDefects
    q r c ε hcone.1 hcone.2.1 hcone.2.2.1 hcone.2.2.2 hc hAbsNear
  dsimp only
  change ‖(1 : SixMat) -
      (labelledSquareA label D + labelledSquareB label D) *
      (labelledSquareA label D + labelledSquareB label D)‖ ≤ 2 * ε
  change ‖(1 : SixMat) -
      (labelledSquareA label D + labelledSquareB label D) *
      (labelledSquareA label D + labelledSquareB label D)‖ =
      1 - (q + r + c) at hNorm
  rw [hNorm]
  exact hGate.1.2

/-- MAN-140/143's original-coordinate corner and isometry
defects are at most twice the positive Pauli overlap slack. -/
theorem sixLabelled_exactHamming_positiveNearHalf_cornerLeakage
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (ε : ℝ)
    (hc : 0 ≤ sixOrientedOppositeEnergyImbalance label D)
    (hnear : (1 / 2 : ℝ) - ε ≤
      sixOrientedOppositeEnergyImbalance label D) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    let X := C * W * C
    let Y := C * W * Q
    ‖X * Y‖ ≤ 2 * ε ∧
      ‖Y.conjTranspose * Y - Q‖ ≤ 2 * ε := by
  dsimp only
  have hDefect := sixLabelled_plusWitness_nonSaturated_normDefect
    label D hD
  have hBound :=
    sixLabelled_exactHamming_positiveNearHalf_defect_norm_le
      label D hD hham ε hc hnear
  dsimp only at hDefect hBound
  exact ⟨hDefect.1.trans hBound, hDefect.2.trans hBound⟩

end Neoplatonic.LTR
