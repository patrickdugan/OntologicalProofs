import Neoplatonic.LTR.SixDimensionalBothSignedSaturationNoGo
import Neoplatonic.LTR.SixDimensionalExactHammingPauliSaturation
import Neoplatonic.LTR.SixDimensionalPauliSaturationSign
import Neoplatonic.LTR.SixDimensionalExactHammingAmbientInvolution
import Neoplatonic.LTR.SixDimensionalSignedWitnessTraceEnergy
import Mathlib.Tactic

/-!
# LTR-MAN-137: maximal positive Pauli overlap forces impossible pure energy

The sharp MAN-85 residual Pauli bound is
  |E03 - E12| <= 1/4.
At positive equality E03-E12=1/4, the true residual Pauli pair has
q_A=q_B=1/4 and real mixed overlap +1/2. The sign-selection theorem
therefore forces the actual two residual matrices to coincide.
Their sum squares to identity. MAN-90 and MAN-91 transport this
involution back to the original 6x6 signed witness W=A+B.

MAN-92 then fixes the trace balance
  6 = 2(m01+m10) + 8 E03.
Faithfulness costs at least two neutral coordinates, while
E03-E12=1/4 and E12>=0 imply E03>=1/4. Equality must hold,
forcing E03=1/4, E12=0, already excluded by MAN-135.

The proof depends on genuine complex Hilbert matrices, without a
postulated U(2) chart. The negative overlap sign will be eliminated
by Boolean-square translation.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- At positive sharp Pauli overlap, the *actual* six-dimensional
signed Hamming witness is a Hermitian involution, without
assuming that either opposite-corner energy vanishes. -/
theorem sixLabelled_exactHamming_positivePauliMax_plus_involution
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hDiff : sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    (labelledSquareA label D + labelledSquareB label D) *
      (labelledSquareA label D + labelledSquareB label D) = 1 := by
  have hsat : |sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2| = (1 / 4 : ℝ) := by
    rw [hDiff]
    norm_num
  obtain ⟨S, hq, hA, hB, hqA, hqB, _⟩ :=
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
    dsimp [sixOrientedOppositeEnergyImbalance]
    rw [hDiff]
    norm_num
  have hMN : M = N :=
    twoDim_pauli_halfSat_positive_select_equal
      M N hMH hNH htrM htrN hqA hqB hc
  have hsum : M + N = (2 : ℂ) • N := by
    rw [hMN]
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hsqN :=
    twoDim_pauli_quarter_double_involution N hNH htrN hqB
  have hMat : (M + N) * (M + N) = 1 := by
    rw [hsum]
    exact hsqN
  have hres := S.residualPlus_involution_of_pauli hq hMat
  have hamb := S.ambientPlus_involution_of_residual hres
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  have hmap : W.toEuclideanLin.toContinuousLinearMap =
      sixLabelledAOperator label D + sixLabelledBOperator label D := by
    change (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)) W =
      (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
        (labelledSquareA label D) +
      (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ))
        (labelledSquareB label D)
    exact map_add (Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)) _ _
  apply sixMatrix_involution_of_trueHilbert_involution W
  rw [hmap]
  simpa only [hA, hB] using hamb

/-- Positive maximum residual Pauli overlap forces the pure
00/11 saturation energy (1/4,0) in every faithful six-dimensional
Dirac chart, using only the actual involution trace identity. -/
theorem sixLabelled_exactHamming_positivePauliMax_forcesPure
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hDiff : sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ) ∧
      sixTruthFibreBlockEnergy label D 1 2 = 0 := by
  have hW := sixLabelled_exactHamming_positivePauliMax_plus_involution
    label D hD hham hDiff
  have hTrace := sixLabelled_plusWitness_involution_trace_energy
    label D hD hW
  have hm1 := truthMultiplicity_pos label hsurj 1
  have hm2 := truthMultiplicity_pos label hsurj 2
  have hmin : 2 ≤ truthMultiplicity label 1 +
      truthMultiplicity label 2 := by omega
  have hminReal :
      (2 : ℝ) ≤
        ((truthMultiplicity label 1 + truthMultiplicity label 2 : ℕ) : ℝ) := by
    exact_mod_cast hmin
  have hE12nonneg :
      (0 : ℝ) ≤ sixTruthFibreBlockEnergy label D 1 2 :=
    sixTruthFibreBlockEnergy_nonneg label D 1 2
  have hTraceReal :
      (6 : ℝ) =
        2 * ((truthMultiplicity label 1 +
          truthMultiplicity label 2 : ℕ) : ℝ) +
          8 * sixTruthFibreBlockEnergy label D 0 3 := by
    apply Complex.ofReal_injective
    exact_mod_cast hTrace
  constructor <;> linarith

/-- The sharp positive Pauli overlap is impossible in the
genuine complex six-dimensional exact-Hamming Connes metric. -/
theorem sixLabelled_exactHamming_positivePauliMax_impossible
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hDiff : sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    False := by
  obtain ⟨h03, h12⟩ :=
    sixLabelled_exactHamming_positivePauliMax_forcesPure
      label D hsurj hD hham hDiff
  exact sixLabelled_exactHamming_saturated03_actualNorm_impossible
    label D hsurj hD hham h03 h12

end Neoplatonic.LTR
