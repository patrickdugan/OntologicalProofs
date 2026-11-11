import Neoplatonic.LTR.SixDimensionalPauliSaturationSign
import Mathlib.Tactic

/-!
# LTR-MAN-88: the surviving opposite Dirac block determines the residual witness sign

For an actual Hermitian six-dimensional labelled Dirac representation
with exact two-bit Hamming Connes distances, MAN-84 identifies the
real residual mixed Pauli coefficient with

  c = 2 (e03 - e12),

where e03, e12 are the one-orientation squared energies of the two
opposite truth-fibre blocks.

At MAN-85's quarter-unit saturation, MAN-87 gives actual
two-dimensional residual matrix equality up to sign. MAN-88
determines that sign:

  e03=1/4, e12=0 => c=+1/2 => M=N, so M-N=0,
  e03=0,   e12=1/4 => c=-1/2 => M=-N, so M+N=0.

In the minimum-one pair multiplicity cases, MAN-86 additionally
gives extinction of the opposite block in both orientations and
rank-one minor certificates for the surviving Dirac block. All
statements share the *same* actual labelled Dirac matrix.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- If 00↔11 carries the entire saturated opposite-corner energy,
the two actual residual Pauli matrices are equal and their
DIFFERENCE vanishes. -/
theorem sixLabelled_exactHamming_saturated03_residualDifference_zero
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
        S.sixDimResidualMatrixA hq (by simp) =
          S.sixDimResidualMatrixB hq (by simp) ∧
        S.sixDimResidualMatrixA hq (by simp) -
          S.sixDimResidualMatrixB hq (by simp) = 0 := by
  have hsat :
      |sixTruthFibreBlockEnergy label D 0 3 -
        sixTruthFibreBlockEnergy label D 1 2| = (1 / 4 : ℝ) := by
    rw [h03, h12]
    norm_num
  obtain ⟨S, hq, hA, hB, hqval, hrval, _⟩ :=
    sixLabelled_exactHamming_energySaturation_residualRigid
      label D hD hham hsat
  have hc : pauliRealMixed
      (S.sixDimResidualMatrixA hq (by simp))
      (S.sixDimResidualMatrixB hq (by simp)) = (1 / 2 : ℝ) := by
    change (pauliMixed (S.sixDimResidualMatrixA hq (by simp))
      (S.sixDimResidualMatrixB hq (by simp))).re = _
    rw [sixLabelled_extremal_pauliMixed_eq_realImbalance
      label D hD S hq hA hB]
    dsimp [sixOrientedOppositeEnergyImbalance]
    rw [h03, h12]
    norm_num
  have heq := twoDim_pauli_halfSat_positive_select_equal
    _ _
    (S.sixDimResidualMatrixA_isHermitian hq (by simp))
    (S.sixDimResidualMatrixB_isHermitian hq (by simp))
    (S.sixDimResidualMatrixA_trace_zero hq (by simp)
      (by rw [hA]; exact (sixLabelled_operatorTrace_zero label D).1))
    (S.sixDimResidualMatrixB_trace_zero hq (by simp)
      (by rw [hB]; exact (sixLabelled_operatorTrace_zero label D).2))
    hqval hrval hc
  refine ⟨S, hq, hA, hB, heq, ?_⟩
  rw [heq]
  simp

/-- If 01↔10 carries the entire saturated opposite-corner energy,
the actual residual Pauli matrices are negatives and their
SUM vanishes. -/
theorem sixLabelled_exactHamming_saturated12_residualSum_zero
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
        S.sixDimResidualMatrixA hq (by simp) =
          -(S.sixDimResidualMatrixB hq (by simp)) ∧
        S.sixDimResidualMatrixA hq (by simp) +
          S.sixDimResidualMatrixB hq (by simp) = 0 := by
  have hsat :
      |sixTruthFibreBlockEnergy label D 0 3 -
        sixTruthFibreBlockEnergy label D 1 2| = (1 / 4 : ℝ) := by
    rw [h03, h12]
    norm_num
  obtain ⟨S, hq, hA, hB, hqval, hrval, _⟩ :=
    sixLabelled_exactHamming_energySaturation_residualRigid
      label D hD hham hsat
  have hc : pauliRealMixed
      (S.sixDimResidualMatrixA hq (by simp))
      (S.sixDimResidualMatrixB hq (by simp)) = -(1 / 2 : ℝ) := by
    change (pauliMixed (S.sixDimResidualMatrixA hq (by simp))
      (S.sixDimResidualMatrixB hq (by simp))).re = _
    rw [sixLabelled_extremal_pauliMixed_eq_realImbalance
      label D hD S hq hA hB]
    dsimp [sixOrientedOppositeEnergyImbalance]
    rw [h03, h12]
    norm_num
  have heq := twoDim_pauli_halfSat_negative_select_opposite
    _ _
    (S.sixDimResidualMatrixA_isHermitian hq (by simp))
    (S.sixDimResidualMatrixB_isHermitian hq (by simp))
    (S.sixDimResidualMatrixA_trace_zero hq (by simp)
      (by rw [hA]; exact (sixLabelled_operatorTrace_zero label D).1))
    (S.sixDimResidualMatrixB_trace_zero hq (by simp)
      (by rw [hB]; exact (sixLabelled_operatorTrace_zero label D).2))
    hqval hrval hc
  refine ⟨S, hq, hA, hB, heq, ?_⟩
  rw [heq]
  simp

/-- In each minimum-one exact-Hamming saturation pattern, the
sign of the residual witness that vanishes is determined by the
surviving opposite-corner Dirac block. The other whole block
vanishes in both orientations; the survivor has rank-one minors. -/
theorem sixLabelled_exactHamming_minOne_saturation_signMatchedBlocks
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hmin03 : min (truthMultiplicity label 0)
      (truthMultiplicity label 3) = 1)
    (hmin12 : min (truthMultiplicity label 1)
      (truthMultiplicity label 2) = 1)
    (hsat : |sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2| = (1 / 4 : ℝ)) :
    ∃ S : TwoDirectionExtremalSystem SixH,
      ∃ hq : Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus),
        S.A = sixLabelledAOperator label D ∧
        S.B = sixLabelledBOperator label D ∧
        ((sixTruthFibreBlock label D 1 2 = 0 ∧
          sixTruthFibreBlock label D 2 1 = 0 ∧
          sixTruthFibreBlock label D 0 3 ≠ 0 ∧
          (∀ i k j l : Fin 6,
            sixTruthFibreBlock label D 0 3 i j *
              sixTruthFibreBlock label D 0 3 k l =
            sixTruthFibreBlock label D 0 3 i l *
              sixTruthFibreBlock label D 0 3 k j) ∧
          S.sixDimResidualMatrixA hq (by simp) -
            S.sixDimResidualMatrixB hq (by simp) = 0) ∨
         (sixTruthFibreBlock label D 0 3 = 0 ∧
          sixTruthFibreBlock label D 3 0 = 0 ∧
          sixTruthFibreBlock label D 1 2 ≠ 0 ∧
          (∀ i k j l : Fin 6,
            sixTruthFibreBlock label D 1 2 i j *
              sixTruthFibreBlock label D 1 2 k l =
            sixTruthFibreBlock label D 1 2 i l *
              sixTruthFibreBlock label D 1 2 k j) ∧
          S.sixDimResidualMatrixA hq (by simp) +
            S.sixDimResidualMatrixB hq (by simp) = 0)) := by
  rcases sixLabelled_exactHamming_minOne_saturation_energyExclusive
    label D hD hham hmin03 hmin12 hsat with
    ⟨h03, h12⟩ | ⟨h03, h12⟩
  · obtain ⟨S, hq, hA, hB, _, hminus⟩ :=
      sixLabelled_exactHamming_saturated03_residualDifference_zero
        label D hD hham h03 h12
    have hz : sixTruthFibreBlock label D 1 2 = 0 :=
      (sixTruthFibreBlockEnergy_zero_iff_block_zero label D 1 2).mp h12
    have hrev := sixTruthFibreBlock_zero_reverse label D hD 1 2 hz
    have hpos : sixTruthFibreBlock label D 0 3 ≠ 0 :=
      sixTruthFibreBlockEnergy_pos_implies_nonzero label D 0 3
        (by rw [h03]; norm_num)
    have hminors : ∀ i k j l : Fin 6,
        sixTruthFibreBlock label D 0 3 i j *
          sixTruthFibreBlock label D 0 3 k l =
        sixTruthFibreBlock label D 0 3 i l *
          sixTruthFibreBlock label D 0 3 k j :=
      fun i k j l =>
        sixTruthFibreBlock_minOne_allTwoByTwoMinors_zero
          label D 0 3 hmin03 i k j l
    exact ⟨S, hq, hA, hB, Or.inl ⟨hz, hrev, hpos, hminors, hminus⟩⟩
  · obtain ⟨S, hq, hA, hB, _, hplus⟩ :=
      sixLabelled_exactHamming_saturated12_residualSum_zero
        label D hD hham h03 h12
    have hz : sixTruthFibreBlock label D 0 3 = 0 :=
      (sixTruthFibreBlockEnergy_zero_iff_block_zero label D 0 3).mp h03
    have hrev := sixTruthFibreBlock_zero_reverse label D hD 0 3 hz
    have hpos : sixTruthFibreBlock label D 1 2 ≠ 0 :=
      sixTruthFibreBlockEnergy_pos_implies_nonzero label D 1 2
        (by rw [h12]; norm_num)
    have hminors : ∀ i k j l : Fin 6,
        sixTruthFibreBlock label D 1 2 i j *
          sixTruthFibreBlock label D 1 2 k l =
        sixTruthFibreBlock label D 1 2 i l *
          sixTruthFibreBlock label D 1 2 k j :=
      fun i k j l =>
        sixTruthFibreBlock_minOne_allTwoByTwoMinors_zero
          label D 1 2 hmin12 i k j l
    exact ⟨S, hq, hA, hB, Or.inr ⟨hz, hrev, hpos, hminors, hplus⟩⟩

end Neoplatonic.LTR
