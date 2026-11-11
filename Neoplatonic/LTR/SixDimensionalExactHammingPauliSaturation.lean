import Neoplatonic.LTR.SixDimensionalPauliSharpHalf
import Mathlib.Tactic

/-!
# LTR-MAN-85: a universal 1/4 bound on actual opposite-corner energy imbalance

MAN-77 derives the norm-saturating signed eigenquartet directly
from all six exact complex Connes Hamming distances. MAN-84
identifies the residual Pauli mixed coefficient with the actual
oriented Hermitian opposite-corner energy imbalance.

MAN-85's sharp Gram inequality gives |c| ≤ 1/2 for *every*
six-dimensional residual system, including both multiplicity
patterns that MAN-84 left with one-sided |c| ≤ 1 estimates.

Thus the oriented squared Dirac coupling energies always obey
  |e03 - e12| ≤ 1/4
without any multiplicity or surjectivity hypotheses.

Equality makes both residual Pauli quadratic coefficients 1/4
and saturates the Pauli Cauchy determinant. With both opposite-pair
minimum dimensions equal to one, the energy equality additionally
forces exactly one opposite-corner block to carry energy 1/4 and
the other to carry zero energy.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Exact two-bit Connes Hamming distances force the real
oriented opposite-corner squared coupling imbalance to be
at most one quarter, in EVERY six-dimensional truth chart. -/
theorem sixLabelled_exactHamming_oppositeEnergyDiff_abs_le_quarter
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    |sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2| ≤ (1 / 4 : ℝ) := by
  obtain ⟨S, hq, hA, hB, _, _⟩ :=
    sixLabelled_exactHamming_oppositeEnergy_budget label D hD hham
  have htrA : LinearMap.trace ℂ SixH S.A.toLinearMap = 0 := by
    rw [hA]
    exact (sixLabelled_operatorTrace_zero label D).1
  have htrB : LinearMap.trace ℂ SixH S.B.toLinearMap = 0 := by
    rw [hB]
    exact (sixLabelled_operatorTrace_zero label D).2
  have hreal :
      pauliRealMixed (S.sixDimResidualMatrixA hq (by simp))
        (S.sixDimResidualMatrixB hq (by simp)) =
      sixOrientedOppositeEnergyImbalance label D := by
    change (pauliMixed (S.sixDimResidualMatrixA hq (by simp))
      (S.sixDimResidualMatrixB hq (by simp))).re = _
    rw [sixLabelled_extremal_pauliMixed_eq_realImbalance
      label D hD S hq hA hB]
    simp
  have hb := S.sixDimResidual_pauliMixed_abs_le_half hq htrA htrB
  rw [hreal] at hb
  change |(2 : ℝ) * (sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2)| ≤ (1 / 2 : ℝ) at hb
  rw [abs_mul] at hb
  norm_num at hb ⊢
  linarith

/-- The real residual Pauli mixed coefficient is universally
bounded by 1/2 for any actual exact-Hamming labelled Dirac system. -/
theorem sixLabelled_exactHamming_universalPauliMixed_half
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
        ‖pauliMixed (S.sixDimResidualMatrixA hq (by simp))
          (S.sixDimResidualMatrixB hq (by simp))‖ ≤ (1 / 2 : ℝ) := by
  obtain ⟨S, hq, hA, hB, _, _⟩ :=
    sixLabelled_exactHamming_oppositeEnergy_budget label D hD hham
  refine ⟨S, hq, hA, hB, ?_⟩
  rw [sixLabelled_extremal_pauliMixed_eq_realImbalance
    label D hD S hq hA hB]
  have hdiff := sixLabelled_exactHamming_oppositeEnergyDiff_abs_le_quarter
    label D hD hham
  have hscale : |sixOrientedOppositeEnergyImbalance label D| ≤
      (1 / 2 : ℝ) := by
    dsimp [sixOrientedOppositeEnergyImbalance]
    rw [abs_mul]
    norm_num at hdiff ⊢
    linarith
  simpa [Complex.norm_real, Real.norm_eq_abs] using hscale

/-- When the actual oriented Dirac energy imbalance saturates
1/4, the signed quartet's residual Pauli vectors are forced to
have squared lengths 1/4 each and zero Gram determinant. -/
theorem sixLabelled_exactHamming_energySaturation_residualRigid
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hsat : |sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2| = (1 / 4 : ℝ)) :
    ∃ S : TwoDirectionExtremalSystem SixH,
      ∃ hq : Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus),
        S.A = sixLabelledAOperator label D ∧
        S.B = sixLabelledBOperator label D ∧
        pauliRealQuadratic (S.sixDimResidualMatrixA hq (by simp)) =
          (1 / 4 : ℝ) ∧
        pauliRealQuadratic (S.sixDimResidualMatrixB hq (by simp)) =
          (1 / 4 : ℝ) ∧
        (pauliRealMixed (S.sixDimResidualMatrixA hq (by simp))
          (S.sixDimResidualMatrixB hq (by simp))) ^ 2 =
          4 * pauliRealQuadratic (S.sixDimResidualMatrixA hq (by simp)) *
            pauliRealQuadratic (S.sixDimResidualMatrixB hq (by simp)) := by
  obtain ⟨S, hq, hA, hB, _, _⟩ :=
    sixLabelled_exactHamming_oppositeEnergy_budget label D hD hham
  have htrA : LinearMap.trace ℂ SixH S.A.toLinearMap = 0 := by
    rw [hA]
    exact (sixLabelled_operatorTrace_zero label D).1
  have htrB : LinearMap.trace ℂ SixH S.B.toLinearMap = 0 := by
    rw [hB]
    exact (sixLabelled_operatorTrace_zero label D).2
  have hreal :
      pauliRealMixed (S.sixDimResidualMatrixA hq (by simp))
        (S.sixDimResidualMatrixB hq (by simp)) =
      sixOrientedOppositeEnergyImbalance label D := by
    change (pauliMixed (S.sixDimResidualMatrixA hq (by simp))
      (S.sixDimResidualMatrixB hq (by simp))).re = _
    rw [sixLabelled_extremal_pauliMixed_eq_realImbalance
      label D hD S hq hA hB]
    simp
  have hsatMixed :
      |pauliRealMixed (S.sixDimResidualMatrixA hq (by simp))
        (S.sixDimResidualMatrixB hq (by simp))| = (1 / 2 : ℝ) := by
    rw [hreal]
    change |(2 : ℝ) * (sixTruthFibreBlockEnergy label D 0 3 -
        sixTruthFibreBlockEnergy label D 1 2)| = (1 / 2 : ℝ)
    rw [abs_mul, hsat]
    norm_num
  obtain ⟨hqval, hrval, hdet⟩ :=
    S.sixDimResidual_half_saturation_rigid hq htrA htrB hsatMixed
  exact ⟨S, hq, hA, hB, hqval, hrval, hdet⟩

/-- In a six-dimensional chart where both opposite-pair minima
are one, attaining maximum Pauli overlap makes one entire
opposite-pair squared energy vanish and the other attain 1/4. -/
theorem sixLabelled_exactHamming_minOne_saturation_energyExclusive
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
    (sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ) ∧
      sixTruthFibreBlockEnergy label D 1 2 = 0) ∨
    (sixTruthFibreBlockEnergy label D 0 3 = 0 ∧
      sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) := by
  obtain ⟨h03, h12⟩ :=
    sixLabelled_exactHamming_oppositeBlock_minEnergy label D hD hham
  have hu : sixTruthFibreBlockEnergy label D 0 3 ≤ (1 / 4 : ℝ) := by
    simpa [hmin03] using h03
  have hv : sixTruthFibreBlockEnergy label D 1 2 ≤ (1 / 4 : ℝ) := by
    simpa [hmin12] using h12
  have hnonneg03 :=
    sixTruthFibreBlockEnergy_nonneg label D 0 3
  have hnonneg12 :=
    sixTruthFibreBlockEnergy_nonneg label D 1 2
  rcases le_total 0 (sixTruthFibreBlockEnergy label D 0 3 -
    sixTruthFibreBlockEnergy label D 1 2) with hpos | hneg
  · have heq := hsat
    rw [abs_of_nonneg hpos] at heq
    exact Or.inl ⟨by linarith, by linarith⟩
  · have heq := hsat
    rw [abs_of_nonpos hneg] at heq
    exact Or.inr ⟨by linarith, by linarith⟩

end Neoplatonic.LTR
