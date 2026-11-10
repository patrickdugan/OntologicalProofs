import Neoplatonic.LTR.SixDimensionalOppositeBlockTraceIdentity
import Neoplatonic.LTR.SixDimensionalOppositeEnergyPatterns
import Mathlib.Tactic

/-!
# LTR-MAN-84: genuine six-dimensional residual Pauli overlap is the oriented energy imbalance

MAN-84 identifies the Hermitian mixed trace with twice the real
difference of the two oriented opposite-corner squared Dirac
coupling energies.

MAN-75/78 transport that mixed trace to the true residual
two-dimensional Pauli matrices. Hence their mixed coefficient
is real and is determined exactly by the opposite-corner
couplings of the *same* Dirac matrix.

For faithful six-dimensional truth-fibre multiplicities, MAN-83
provides three sharp numerical rectangles for the oriented energies.
The signed Pauli mixed coefficient consequently has one of three
real intervals. When both opposite-pair minimum multiplicities
are one, its complex magnitude is at most one half.

The 6D Hamming existence question remains open; these are
necessary constraints under its exact Connes distances.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The actual real signed opposite-corner energy imbalance
of the Hermitian six-dimensional Dirac matrix. -/
noncomputable def sixOrientedOppositeEnergyImbalance
    (label : Fin 6 → Fin 4) (D : SixMat) : ℝ :=
  2 * (sixTruthFibreBlockEnergy label D 0 3 -
       sixTruthFibreBlockEnergy label D 1 2)

/-- Each oriented truth-fibre squared coupling energy is
nonnegative as a finite sum of real squares. -/
theorem sixTruthFibreBlockEnergy_nonneg
    (label : Fin 6 → Fin 4) (D : SixMat)
    (u v : Fin 4) :
    0 ≤ sixTruthFibreBlockEnergy label D u v := by
  unfold sixTruthFibreBlockEnergy
  apply Finset.sum_nonneg
  intro j hj
  apply Finset.sum_nonneg
  intro i hi
  exact sq_nonneg _

/-- The true two-dimensional residual Pauli coefficient is
exactly the real oriented opposite-corner Dirac energy imbalance
for any labelled Hermitian Dirac extremal system. -/
theorem sixLabelled_extremal_pauliMixed_eq_realImbalance
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (S : TwoDirectionExtremalSystem SixH)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hA : S.A = sixLabelledAOperator label D)
    (hB : S.B = sixLabelledBOperator label D) :
    pauliMixed (S.sixDimResidualMatrixA hq (by simp))
      (S.sixDimResidualMatrixB hq (by simp)) =
        ((sixOrientedOppositeEnergyImbalance label D : ℝ) : ℂ) := by
  calc
    pauliMixed (S.sixDimResidualMatrixA hq (by simp))
        (S.sixDimResidualMatrixB hq (by simp)) =
        (labelledSquareA label D * labelledSquareB label D).trace :=
      sixLabelled_extremal_pauliMixed_eq_matrixTrace label D S hq hA hB
    _ = ((sixOrientedOppositeEnergyImbalance label D : ℝ) : ℂ) := by
      exact sixLabelled_crossTrace_eq_two_orientedEnergyDifference
        label D hD

/-- The actual real Pauli three-vectors on the residual have
inner product equal to the *oriented* squared coupling difference. -/
theorem sixLabelled_extremal_pauliDot_eq_blockEnergyDifference
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (S : TwoDirectionExtremalSystem SixH)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hA : S.A = sixLabelledAOperator label D)
    (hB : S.B = sixLabelledBOperator label D) :
    pauliRealDot (S.sixDimResidualMatrixA hq (by simp))
      (S.sixDimResidualMatrixB hq (by simp)) =
        sixTruthFibreBlockEnergy label D 0 3 -
          sixTruthFibreBlockEnergy label D 1 2 := by
  let M := S.sixDimResidualMatrixA hq (by simp)
  let N := S.sixDimResidualMatrixB hq (by simp)
  have hC : pauliMixed M N =
      ((sixOrientedOppositeEnergyImbalance label D : ℝ) : ℂ) :=
    sixLabelled_extremal_pauliMixed_eq_realImbalance
      label D hD S hq hA hB
  have hReal : pauliRealMixed M N =
      sixOrientedOppositeEnergyImbalance label D := by
    change (pauliMixed M N).re = _
    rw [hC]
    simp
  have hDot := pauliRealMixed_eq_two_dot M N
    (S.sixDimResidualMatrixA_isHermitian hq (by simp))
    (S.sixDimResidualMatrixB_isHermitian hq (by simp))
  rw [hReal] at hDot
  dsimp only [sixOrientedOppositeEnergyImbalance] at hDot
  dsimp only [M, N] at *
  linarith

/-- The ten faithful six-dimensional fibre assignments yield
three possible intervals for the *real* mixed Pauli coefficient,
which is exactly the actual oriented Dirac energy imbalance. -/
theorem sixLabelled_exactHamming_realPauli_threeIntervals
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    ∃ S : TwoDirectionExtremalSystem SixH,
      ∃ hq : Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus),
        S.A = sixLabelledAOperator label D ∧
        S.B = sixLabelledBOperator label D ∧
        pauliMixed (S.sixDimResidualMatrixA hq (by simp))
          (S.sixDimResidualMatrixB hq (by simp)) =
          ((sixOrientedOppositeEnergyImbalance label D : ℝ) : ℂ) ∧
        ((-(1 / 2 : ℝ) ≤ sixOrientedOppositeEnergyImbalance label D ∧
            sixOrientedOppositeEnergyImbalance label D ≤ 1 / 2) ∨
         (-(1 / 2 : ℝ) ≤ sixOrientedOppositeEnergyImbalance label D ∧
            sixOrientedOppositeEnergyImbalance label D ≤ 1) ∨
         (-(1 : ℝ) ≤ sixOrientedOppositeEnergyImbalance label D ∧
            sixOrientedOppositeEnergyImbalance label D ≤ 1 / 2)) := by
  obtain ⟨S, hq, hA, hB, _, _⟩ :=
    sixLabelled_exactHamming_oppositeEnergy_budget label D hD hham
  refine ⟨S, hq, hA, hB, ?_, ?_⟩
  · exact sixLabelled_extremal_pauliMixed_eq_realImbalance
      label D hD S hq hA hB
  · have hn03 : 0 ≤ sixTruthFibreBlockEnergy label D 0 3 :=
      sixTruthFibreBlockEnergy_nonneg label D 0 3
    have hn12 : 0 ≤ sixTruthFibreBlockEnergy label D 1 2 :=
      sixTruthFibreBlockEnergy_nonneg label D 1 2
    rcases sixLabelled_exactHamming_oppositeEnergy_threeCases
      label D hsurj hD hham with
      ⟨h03, h12⟩ | ⟨h03, h12⟩ | ⟨h03, h12⟩
    · exact Or.inl ⟨by
        dsimp [sixOrientedOppositeEnergyImbalance]
        linarith, by
        dsimp [sixOrientedOppositeEnergyImbalance]
        linarith⟩
    · exact Or.inr (Or.inl ⟨by
        dsimp [sixOrientedOppositeEnergyImbalance]
        linarith, by
        dsimp [sixOrientedOppositeEnergyImbalance]
        linarith⟩)
    · exact Or.inr (Or.inr ⟨by
        dsimp [sixOrientedOppositeEnergyImbalance]
        linarith, by
        dsimp [sixOrientedOppositeEnergyImbalance]
        linarith⟩)

/-- The eight faithful six-dimensional patterns whose two
opposite-pair minima both equal one admit the sharper mixed
coefficient magnitude bound |c| ≤ 1/2. -/
theorem sixLabelled_exactHamming_oppositeMinOne_pauliMixed_half
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hmin03 : min (truthMultiplicity label 0)
      (truthMultiplicity label 3) = 1)
    (hmin12 : min (truthMultiplicity label 1)
      (truthMultiplicity label 2) = 1) :
    ∃ S : TwoDirectionExtremalSystem SixH,
      ∃ hq : Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus),
        S.A = sixLabelledAOperator label D ∧
        S.B = sixLabelledBOperator label D ∧
        ‖pauliMixed (S.sixDimResidualMatrixA hq (by simp))
          (S.sixDimResidualMatrixB hq (by simp))‖ ≤ (1 / 2 : ℝ) := by
  obtain ⟨h03, h12⟩ :=
    sixLabelled_exactHamming_oppositeBlock_minEnergy label D hD hham
  have hb03 : sixTruthFibreBlockEnergy label D 0 3 ≤ (1 / 4 : ℝ) := by
    simpa [hmin03] using h03
  have hb12 : sixTruthFibreBlockEnergy label D 1 2 ≤ (1 / 4 : ℝ) := by
    simpa [hmin12] using h12
  have hn03 : 0 ≤ sixTruthFibreBlockEnergy label D 0 3 :=
    sixTruthFibreBlockEnergy_nonneg label D 0 3
  have hn12 : 0 ≤ sixTruthFibreBlockEnergy label D 1 2 :=
    sixTruthFibreBlockEnergy_nonneg label D 1 2
  have hr : |sixOrientedOppositeEnergyImbalance label D| ≤ (1 / 2 : ℝ) := by
    apply abs_le.mpr
    constructor <;> dsimp [sixOrientedOppositeEnergyImbalance] <;>
      linarith
  obtain ⟨S, hq, hA, hB, _, _⟩ :=
    sixLabelled_exactHamming_oppositeEnergy_budget label D hD hham
  refine ⟨S, hq, hA, hB, ?_⟩
  rw [sixLabelled_extremal_pauliMixed_eq_realImbalance
    label D hD S hq hA hB]
  simpa [Complex.norm_real, Real.norm_eq_abs] using hr

end Neoplatonic.LTR
