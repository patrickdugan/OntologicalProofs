import Neoplatonic.LTR.SixDimensionalResidualPauliHalfSatEquality
import Mathlib.Tactic

/-!
# LTR-MAN-87: exact Hamming saturation extinguishes one residual witness

MAN-85 proves that quarter-unit opposite Dirac energy imbalance
saturation makes the actual two-dimensional residual Pauli mixed
coefficient have absolute value 1/2.

The MAN-87 real-vector and Hermitian normal-form theorem then proves
that the actual residual A and B matrices coincide up to sign.
Consequently one of the two residual signed Hamming witnesses
A-B and A+B vanishes on the entire common two-dimensional
orthogonal complement to the signed eigenquartet.

MAN-86 separately constrains the original full six-dimensional
Dirac matrix: under both minimum opposite-pair multiplicities 1,
the surviving opposite block is rank one and the other is zero.
Both spectral and truth-fibre conclusions now come from the same
exact-Hamming and saturation hypotheses.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- At exact-Hamming quarter-imbalance saturation the true
six-dimensional labelled Dirac extremal system has residual
2×2 coordinate operators equal up to sign, in the same basis. -/
theorem sixLabelled_exactHamming_energySat_residualPauli_equalOrNeg
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
        (S.sixDimResidualMatrixA hq (by simp) =
          S.sixDimResidualMatrixB hq (by simp) ∨
         S.sixDimResidualMatrixA hq (by simp) =
          -(S.sixDimResidualMatrixB hq (by simp))) := by
  obtain ⟨S, hq, hA, hB, _, _, _⟩ :=
    sixLabelled_exactHamming_energySaturation_residualRigid
      label D hD hham hsat
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
  exact ⟨S, hq, hA, hB,
    S.sixDimResidual_halfSat_matrixEqualOrNeg hq htrA htrB hsatMixed⟩

/-- The same exact-Hamming saturation hypothesis forces
one entire signed-witness matrix to vanish on the two-dimensional
spectral residual: either A-B or A+B has zero residual matrix. -/
theorem sixLabelled_exactHamming_energySat_residualWitness_zero
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
        (S.sixDimResidualMatrixA hq (by simp) -
          S.sixDimResidualMatrixB hq (by simp) = 0 ∨
         S.sixDimResidualMatrixA hq (by simp) +
          S.sixDimResidualMatrixB hq (by simp) = 0) := by
  obtain ⟨S, hq, hA, hB, hpm⟩ :=
    sixLabelled_exactHamming_energySat_residualPauli_equalOrNeg
      label D hD hham hsat
  refine ⟨S, hq, hA, hB, ?_⟩
  rcases hpm with hp | hm
  · left
    rw [hp]
    simp
  · right
    rw [hm]
    simp

end Neoplatonic.LTR
