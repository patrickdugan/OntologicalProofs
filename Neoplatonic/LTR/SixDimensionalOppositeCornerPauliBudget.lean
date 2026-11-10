import Neoplatonic.LTR.SixDimensionalOppositeCornerTrace
import Neoplatonic.LTR.SixDimensionalLabelledPauliBridge
import Mathlib.Tactic

/-!
# LTR-MAN-78: the exact-Hamming Pauli residual measures opposite-corner imbalance

MAN-78 proves trace(A B) = E03 - E12 for the actual labelled
coordinate Dirac commutators. MAN-75/76 identify that ambient mixed
trace with the residual Pauli mixed coefficient. MAN-77 constructs the
genuine extremal system from the six exact Connes dual Hamming distances.

The two opposite witness contractions also bound the complex
mixed Pauli coefficient by one. We therefore obtain:

    c = E03 - E12,     ‖E03 - E12‖ ≤ 1.

A balanced pair E03 = E12 makes the genuine residual Pauli vectors
orthogonal, even if opposite-corner couplings are individually nonzero.

This is a necessary condition and does not decide realization of
the six-dimensional Hamming metric.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The two contractions on x ± c bound the mixed scalar
coefficient c by one, purely in the complex normed field. -/
theorem complex_twoSided_mixed_norm_le_one
    (x c : ℂ)
    (hp : ‖x + c‖ ≤ 1)
    (hm : ‖x - c‖ ≤ 1) :
    ‖c‖ ≤ 1 := by
  have heq : (2 : ℂ) • c = (x + c) - (x - c) := by
    module
  have hb : ‖(2 : ℂ) • c‖ ≤ (2 : ℝ) := by
    rw [heq]
    calc
      ‖(x + c) - (x - c)‖ ≤
          ‖x + c‖ + ‖x - c‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith
  rw [norm_smul] at hb
  norm_num at hb
  linarith

/-- For any actual residual extrema, the mixed Pauli coefficient
is precisely the difference of the labelled Dirac opposite energies. -/
theorem sixLabelled_extremal_oppositeEnergy_eq_pauliMixed
    (label : Fin 6 → Fin 4) (D : SixMat)
    (S : TwoDirectionExtremalSystem SixH)
    (hq : Orthonormal ℂ
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus))
    (hA : S.A = sixLabelledAOperator label D)
    (hB : S.B = sixLabelledBOperator label D) :
    pauliMixed (S.sixDimResidualMatrixA hq (by simp))
      (S.sixDimResidualMatrixB hq (by simp)) =
        labelledOpposite03Energy label D -
          labelledOpposite12Energy label D := by
  calc
    pauliMixed (S.sixDimResidualMatrixA hq (by simp))
        (S.sixDimResidualMatrixB hq (by simp)) =
      (labelledSquareA label D * labelledSquareB label D).trace :=
      sixLabelled_extremal_pauliMixed_eq_matrixTrace label D S hq hA hB
    _ = labelledOpposite03Energy label D -
          labelledOpposite12Energy label D :=
      labelledSquare_crossTrace_eq_energyDifference label D

/-- An actual signed eigenquartet under all six exact Hamming Connes
distances has opposite-corner energy imbalance of norm at most one.
It also identifies that imbalance with the residual Pauli pairing. -/
theorem sixLabelled_exactHamming_oppositeEnergy_budget
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
        pauliMixed (S.sixDimResidualMatrixA hq (by simp))
          (S.sixDimResidualMatrixB hq (by simp)) =
          labelledOpposite03Energy label D -
            labelledOpposite12Energy label D ∧
        ‖labelledOpposite03Energy label D -
            labelledOpposite12Energy label D‖ ≤ 1 := by
  have hd01 : sixLabelledConnesDistance label D 0 1 = 1 := by
    simpa [twoBitSquareHamming] using hham 0 1
  have hd02 : sixLabelledConnesDistance label D 0 2 = 1 := by
    simpa [twoBitSquareHamming] using hham 0 2
  have hd31 : sixLabelledConnesDistance label D 3 1 = 1 := by
    simpa [twoBitSquareHamming] using hham 3 1
  have hd32 : sixLabelledConnesDistance label D 3 2 = 1 := by
    simpa [twoBitSquareHamming] using hham 3 2
  have hd03 : sixLabelledConnesDistance label D 0 3 = 2 := by
    simpa [twoBitSquareHamming] using hham 0 3
  have hd12 : sixLabelledConnesDistance label D 1 2 = 2 := by
    simpa [twoBitSquareHamming] using hham 1 2
  obtain ⟨S, hq, hA, hB⟩ :=
    sixLabelled_exactHamming_exists_extremalSystem
      label D hD hd01 hd02 hd31 hd32 hd03 hd12
  have hta : LinearMap.trace ℂ SixH S.A.toLinearMap = 0 := by
    rw [hA]
    exact (sixLabelled_operatorTrace_zero label D).1
  have htb : LinearMap.trace ℂ SixH S.B.toLinearMap = 0 := by
    rw [hB]
    exact (sixLabelled_operatorTrace_zero label D).2
  obtain ⟨hp, hm⟩ :=
    S.sixDimResidual_pauliCoefficients_le_one hq (by simp) hta htb
  have hnorm :
      ‖pauliMixed (S.sixDimResidualMatrixA hq (by simp))
        (S.sixDimResidualMatrixB hq (by simp))‖ ≤ 1 :=
    complex_twoSided_mixed_norm_le_one
      (pauliQuadratic (S.sixDimResidualMatrixA hq (by simp)) +
        pauliQuadratic (S.sixDimResidualMatrixB hq (by simp)))
      (pauliMixed (S.sixDimResidualMatrixA hq (by simp))
        (S.sixDimResidualMatrixB hq (by simp))) hp hm
  have heq := sixLabelled_extremal_oppositeEnergy_eq_pauliMixed
    label D S hq hA hB
  refine ⟨S, hq, hA, hB, heq, ?_⟩
  rwa [heq] at hnorm

/-- A second useful consequence: equality of the two labelled
opposite-corner energies forces orthogonality of the true real Pauli
residual vectors, without separately assuming either energy zero. -/
theorem sixLabelled_exactHamming_balancedOpposites_pauliOrthogonal
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hbalance : labelledOpposite03Energy label D =
      labelledOpposite12Energy label D) :
    ∃ S : TwoDirectionExtremalSystem SixH,
      ∃ hq : Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus),
        S.A = sixLabelledAOperator label D ∧
        S.B = sixLabelledBOperator label D ∧
        pauliRealDot (S.sixDimResidualMatrixA hq (by simp))
          (S.sixDimResidualMatrixB hq (by simp)) = 0 := by
  obtain ⟨S, hq, hA, hB, heq, _⟩ :=
    sixLabelled_exactHamming_oppositeEnergy_budget label D hD hham
  refine ⟨S, hq, hA, hB, ?_⟩
  let M := S.sixDimResidualMatrixA hq (by simp)
  let N := S.sixDimResidualMatrixB hq (by simp)
  have hc : pauliMixed M N = 0 := by
    simpa only [hbalance, sub_self] using heq
  have hr : pauliRealMixed M N = 0 := by
    simp [pauliRealMixed, hc]
  have hdot := pauliRealMixed_eq_two_dot M N
    (S.sixDimResidualMatrixA_isHermitian hq (by simp))
    (S.sixDimResidualMatrixB_isHermitian hq (by simp))
  rw [hr] at hdot
  dsimp only [M, N] at *
  linarith

end Neoplatonic.LTR
