import Neoplatonic.LTR.SixDimensionalBothSignedSaturationNoGo
import Neoplatonic.LTR.SixDimensionalSignedWitnessTraceEnergy
import Neoplatonic.LTR.SixDimensionalExactHammingPauliSaturation
import Neoplatonic.LTR.SixDimensionalPauliSaturationSign
import Mathlib.Tactic

/-!
# LTR-MAN-137: positive endpoint Pauli imbalance forces impossible pure saturation

MAN-85 shows |E03-E12| <= 1/4 for a genuine exact-Hamming six-dimensional
Dirac matrix. At E03-E12=1/4, its real residual Pauli mixed term is
+1/2, and the real Pauli quadratic lengths are both 1/4.
The sign-selected residual Pauli matrices therefore coincide.

Twice their common matrix squares to identity. The genuine Hilbert
residual/ambient lifting of MAN-90/91 then proves W+²=I₆. MAN-92's
full trace identity gives 6=2(m01+m10)+8E03. Faithfulness implies
m01+m10>=2, hence E03<=1/4. With E03-E12=1/4 and E12>=0,
we must have E03=1/4 and E12=0, excluded by MAN-135/136.

This closes the positive signed endpoint of the universal Pauli
inequality without assuming in advance that either opposite block
vanishes. The negative endpoint follows by Boolean translation.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The positive maximum energy imbalance already forces the
original six-dimensional signed Hamming witness to be involutive. -/
theorem sixLabelled_exactHamming_maxPositiveImbalance_plusInvolution
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hsign : sixTruthFibreBlockEnergy label D 0 3 -
        sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    (labelledSquareA label D + labelledSquareB label D) *
      (labelledSquareA label D + labelledSquareB label D) = 1 := by
  have hsat : |sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2| = (1 / 4 : ℝ) := by
    rw [hsign]
    norm_num
  obtain ⟨S, hq, hA, hB, hqM, hqN, _⟩ :=
    sixLabelled_exactHamming_energySaturation_residualRigid
      label D hD hham hsat
  let M := S.sixDimResidualMatrixA hq (by simp)
  let N := S.sixDimResidualMatrixB hq (by simp)
  have hMH : M.IsHermitian :=
    S.sixDimResidualMatrixA_isHermitian hq (by simp)
  have hNH : N.IsHermitian :=
    S.sixDimResidualMatrixB_isHermitian hq (by simp)
  have htrM : M.trace = 0 :=
    S.sixDimResidualMatrixA_trace_zero hq (by simp)
      (by rw [hA]; exact (sixLabelled_operatorTrace_zero label D).1)
  have htrN : N.trace = 0 :=
    S.sixDimResidualMatrixB_trace_zero hq (by simp)
      (by rw [hB]; exact (sixLabelled_operatorTrace_zero label D).2)
  have hc : pauliRealMixed M N = (1 / 2 : ℝ) := by
    change (pauliMixed M N).re = _
    rw [sixLabelled_extremal_pauliMixed_eq_realImbalance
      label D hD S hq hA hB]
    change (2 * (sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2) : ℝ) = _
    rw [hsign]
    norm_num
  have hMN : M = N :=
    twoDim_pauli_halfSat_positive_select_equal
      M N hMH hNH htrM htrN hqM hqN hc
  have hsum : M + N = (2 : ℂ) • N := by
    rw [hMN]
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hsq : (M + N) * (M + N) = 1 := by
    rw [hsum]
    exact twoDim_pauli_quarter_double_involution N hNH htrN hqN
  have hres := S.residualPlus_involution_of_pauli hq hsq
  have hamb := S.ambientPlus_involution_of_residual hres
  have hamb' :
      (sixLabelledAOperator label D + sixLabelledBOperator label D) *
        (sixLabelledAOperator label D + sixLabelledBOperator label D) = 1 := by
    simpa only [hA, hB] using hamb
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  have hmap : W.toEuclideanLin.toContinuousLinearMap =
      sixLabelledAOperator label D + sixLabelledBOperator label D := by
    change (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)) W =
      (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
        (labelledSquareA label D) +
      (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
        (labelledSquareB label D)
    exact map_add (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)) _ _
  change W * W = 1
  apply sixMatrix_involution_of_trueHilbert_involution W
  rw [hmap]
  exact hamb'

/-- The positive maximal Pauli overlap equality forces the
already-excluded pure positive opposite-block energy pattern,
through the genuine W+ trace budget. -/
theorem sixLabelled_exactHamming_maxPositiveImbalance_pure
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hsign : sixTruthFibreBlockEnergy label D 0 3 -
        sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ) ∧
      sixTruthFibreBlockEnergy label D 1 2 = 0 := by
  have hW :=
    sixLabelled_exactHamming_maxPositiveImbalance_plusInvolution
      label D hD hham hsign
  have htrace := sixLabelled_plusWitness_involution_trace_energy
    label D hD hW
  have hMul1 : 1 ≤ truthMultiplicity label 1 :=
    truthMultiplicity_pos label hsurj 1
  have hMul2 : 1 ≤ truthMultiplicity label 2 :=
    truthMultiplicity_pos label hsurj 2
  have hN : 2 ≤ truthMultiplicity label 1 +
      truthMultiplicity label 2 := by omega
  have htraceReal :
      (6 : ℝ) =
        2 * ((truthMultiplicity label 1 +
          truthMultiplicity label 2 : ℕ) : ℝ) +
        8 * sixTruthFibreBlockEnergy label D 0 3 := by
    exact_mod_cast htrace
  have hNreal :
      (2 : ℝ) ≤ ((truthMultiplicity label 1 +
        truthMultiplicity label 2 : ℕ) : ℝ) := by
    exact_mod_cast hN
  have h12nonneg :=
    sixTruthFibreBlockEnergy_nonneg label D 1 2
  have he03 : sixTruthFibreBlockEnergy label D 0 3 =
      (1 / 4 : ℝ) := by
    linarith
  have he12 : sixTruthFibreBlockEnergy label D 1 2 = 0 := by
    linarith
  exact ⟨he03, he12⟩

/-- The extremal positive Pauli imbalance is impossible in every
faithful six-dimensional exact-Hamming Dirac representation. -/
theorem sixLabelled_exactHamming_maxPositiveImbalance_impossible
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hsign : sixTruthFibreBlockEnergy label D 0 3 -
        sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    False := by
  obtain ⟨he03, he12⟩ :=
    sixLabelled_exactHamming_maxPositiveImbalance_pure
      label D hsurj hD hham hsign
  exact sixLabelled_exactHamming_saturated03_actualNorm_impossible
    label D hsurj hD hham he03 he12

end Neoplatonic.LTR
