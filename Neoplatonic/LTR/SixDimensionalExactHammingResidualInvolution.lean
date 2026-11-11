import Neoplatonic.LTR.SixDimensionalResidualPauliInvolution
import Mathlib.Tactic

/-!
# LTR-MAN-89: the saturated residual signed Hamming witness squares to identity

MAN-88 selects the correct residual witness according to which opposite
truth diagonal carries the quarter-unit oriented Dirac energy:
  00--11 survival: residual M=N;
  01--10 survival: residual M=-N.

The mixed Pauli coefficient is ±1/2, so the self-overlap identity
c(M,M)=2q_M identifies the surviving residual Pauli square coefficient
q=1/4. The matrix lemma in MAN-89 then proves the surviving signed
witness *squares to the full two-dimensional identity matrix*.

The other witness vanishes as a complete residual matrix, from MAN-88.
These are true residual matrices obtained in the SAME orthonormal
basis and from the SAME Hermitian six-dimensional Dirac matrix.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- If the 00--11 opposite block carries saturated energy, the
sum Hamming witness is an exact involution on the true 2D residual
and the difference witness vanishes there. -/
theorem sixLabelled_exactHamming_saturated03_residualPlus_involution
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    ∃ S : TwoDirectionExtremalSystem SixH,
      ∃ hq : Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus),
        S.A = sixLabelledAOperator label D ∧
        S.B = sixLabelledBOperator label D ∧
        (S.sixDimResidualMatrixA hq (by simp) +
           S.sixDimResidualMatrixB hq (by simp)) *
          (S.sixDimResidualMatrixA hq (by simp) +
           S.sixDimResidualMatrixB hq (by simp)) = 1 ∧
        S.sixDimResidualMatrixA hq (by simp) -
          S.sixDimResidualMatrixB hq (by simp) = 0 := by
  obtain ⟨S, hq, hA, hB, hMN, hminus⟩ :=
    sixLabelled_exactHamming_saturated03_residualDifference_zero
      label D hD hham h03 h12
  let M := S.sixDimResidualMatrixA hq (by simp)
  let N := S.sixDimResidualMatrixB hq (by simp)
  have hc : pauliRealMixed M N = (1 / 2 : ℝ) := by
    change (pauliMixed M N).re = _
    rw [sixLabelled_extremal_pauliMixed_eq_realImbalance
      label D hD S hq hA hB]
    dsimp [sixOrientedOppositeEnergyImbalance]
    rw [h03, h12]
    norm_num
  have hN : N.IsHermitian :=
    S.sixDimResidualMatrixB_isHermitian hq (by simp)
  have htrN : N.trace = 0 :=
    S.sixDimResidualMatrixB_trace_zero hq (by simp)
      (by rw [hB]; exact (sixLabelled_operatorTrace_zero label D).2)
  have hqN : pauliRealQuadratic N = (1 / 4 : ℝ) := by
    change M = N at hMN
    rw [hMN, pauliRealMixed_self_eq_twoQuadratic N hN] at hc
    linarith
  have hsum : M + N = (2 : ℂ) • N := by
    rw [hMN]
    ext i j
    simp [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hsq := twoDim_pauli_quarter_double_involution N hN htrN hqN
  refine ⟨S, hq, hA, hB, ?_, hminus⟩
  change (M + N) * (M + N) = 1
  rw [hsum]
  exact hsq

/-- If the 01--10 opposite block carries saturated energy, the
difference Hamming witness is an exact involution on the true 2D
residual and the sum witness vanishes there. -/
theorem sixLabelled_exactHamming_saturated12_residualMinus_involution
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = 0)
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    ∃ S : TwoDirectionExtremalSystem SixH,
      ∃ hq : Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus),
        S.A = sixLabelledAOperator label D ∧
        S.B = sixLabelledBOperator label D ∧
        (S.sixDimResidualMatrixA hq (by simp) -
           S.sixDimResidualMatrixB hq (by simp)) *
          (S.sixDimResidualMatrixA hq (by simp) -
           S.sixDimResidualMatrixB hq (by simp)) = 1 ∧
        S.sixDimResidualMatrixA hq (by simp) +
          S.sixDimResidualMatrixB hq (by simp) = 0 := by
  obtain ⟨S, hq, hA, hB, hMN, hplus⟩ :=
    sixLabelled_exactHamming_saturated12_residualSum_zero
      label D hD hham h03 h12
  let M := S.sixDimResidualMatrixA hq (by simp)
  let N := S.sixDimResidualMatrixB hq (by simp)
  have hc : pauliRealMixed M N = -(1 / 2 : ℝ) := by
    change (pauliMixed M N).re = _
    rw [sixLabelled_extremal_pauliMixed_eq_realImbalance
      label D hD S hq hA hB]
    dsimp [sixOrientedOppositeEnergyImbalance]
    rw [h03, h12]
    norm_num
  have hN : N.IsHermitian :=
    S.sixDimResidualMatrixB_isHermitian hq (by simp)
  have htrN : N.trace = 0 :=
    S.sixDimResidualMatrixB_trace_zero hq (by simp)
      (by rw [hB]; exact (sixLabelled_operatorTrace_zero label D).2)
  have hqN : pauliRealQuadratic N = (1 / 4 : ℝ) := by
    change M = -N at hMN
    rw [hMN, pauliRealMixed_neg_left,
      pauliRealMixed_self_eq_twoQuadratic N hN] at hc
    linarith
  have hdiff : M - N = -((2 : ℂ) • N) := by
    rw [hMN]
    ext i j
    simp [Matrix.sub_apply, Matrix.neg_apply,
      Matrix.smul_apply, smul_eq_mul]
    ring
  have hsq := twoDim_pauli_quarter_negDouble_involution N hN htrN hqN
  refine ⟨S, hq, hA, hB, ?_, hplus⟩
  change (M - N) * (M - N) = 1
  rw [hdiff]
  exact hsq

end Neoplatonic.LTR
