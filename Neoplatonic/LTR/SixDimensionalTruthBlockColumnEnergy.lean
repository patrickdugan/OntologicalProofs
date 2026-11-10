import Neoplatonic.LTR.SixDimensionalOppositeFibreBlockNorm
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# LTR-MAN-81: rank-sensitive column energy budgets for truth blocks

MAN-80 proves that each full opposite-corner truth-fibre block
has Euclidean Hilbert operator norm at most one half under exact
Hamming Connes distances.

For any 6×6 complex matrix M, apply the operator to the coordinate
unit vector e_j. Its squared Hilbert norm is the sum over the jth
column of squared complex entry norms. Thus

  ∑_i ‖M_ij‖² ≤ ‖M‖op².

A truth-fibre block Q_u D Q_v has zero columns outside the v fibre.
Summing just its nonzero columns gives

  ∑_ij ‖(Q_u D Q_v)_ij‖² ≤ multiplicity(v)/4,

when the full block norm is at most one half.

This is a bound on the *whole block energy*, sensitive to truth-fibre
multiplicity and the complete Hilbert operator norm, rather than
the individual entrywise bound from MAN-79.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- One column's sum of squared complex entry magnitudes is
bounded by the squared Euclidean Hilbert operator norm. -/
theorem sixMatrix_columnEnergy_le_operatorNorm_sq
    (M : SixMat) (j : Fin 6) :
    (∑ i : Fin 6, ‖M i j‖ ^ 2) ≤ ‖M‖ ^ 2 := by
  let e : SixH := PiLp.single (2 : ℝ≥0∞) j (1 : ℂ)
  have he : ‖e‖ = 1 := by simp [e]
  have hvec (i : Fin 6) :
      (M.toEuclideanLin.toContinuousLinearMap e) i = M i j := by
    change (((Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)) M)
      (WithLp.toLp 2 (Pi.single j (1 : ℂ)))) i = M i j
    rw [Matrix.toEuclideanCLM_toLp]
    simp [Matrix.mulVec_single_one]
  have hle :
      ‖M.toEuclideanLin.toContinuousLinearMap e‖ ≤ ‖M‖ := by
    calc
      ‖M.toEuclideanLin.toContinuousLinearMap e‖ ≤
          ‖M.toEuclideanLin.toContinuousLinearMap‖ * ‖e‖ :=
        (M.toEuclideanLin.toContinuousLinearMap).le_opNorm e
      _ = ‖M‖ := by rw [he, mul_one]; rfl
  have hsq :
      ‖M.toEuclideanLin.toContinuousLinearMap e‖ ^ 2 ≤ ‖M‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hle
  calc
    (∑ i : Fin 6, ‖M i j‖ ^ 2) =
        ‖M.toEuclideanLin.toContinuousLinearMap e‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hvec i]
    _ ≤ ‖M‖ ^ 2 := hsq

/-- Squared coupling energy of a full six-dimensional truth block,
counting each oriented matrix entry once. -/
noncomputable def sixTruthFibreBlockEnergy
    (label : Fin 6 → Fin 4) (D : SixMat)
    (u v : Fin 4) : ℝ :=
  ∑ j : Fin 6, ∑ i : Fin 6,
    ‖sixTruthFibreBlock label D u v i j‖ ^ 2

/-- The energy of a truth-fibre block bounded by 1/2 in operator
norm costs at most one quarter per coordinate in its input fibre.
The proof includes all off-block zero columns exactly. -/
theorem sixTruthFibreBlockEnergy_le_inputMultiplicity_quarter
    (label : Fin 6 → Fin 4) (D : SixMat)
    (u v : Fin 4)
    (hnorm : ‖sixTruthFibreBlock label D u v‖ ≤ (1 / 2 : ℝ)) :
    sixTruthFibreBlockEnergy label D u v ≤
      (truthMultiplicity label v : ℝ) / 4 := by
  let B : SixMat := sixTruthFibreBlock label D u v
  have hcol (j : Fin 6) :
      (∑ i : Fin 6, ‖B i j‖ ^ 2) ≤
        if label j = v then (1 / 4 : ℝ) else 0 := by
    by_cases hj : label j = v
    · have hbound := sixMatrix_columnEnergy_le_operatorNorm_sq B j
      have hsquare : ‖B‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg B) (by norm_num)).mpr hnorm
      simp only [if_pos hj]
      nlinarith
    · have hzero (i : Fin 6) : B i j = 0 := by
        change sixTruthFibreBlock label D u v i j = 0
        rw [sixTruthFibreBlock_entry]
        simp [hj]
      simp [hj, hzero]
  have hsum :
      (∑ j : Fin 6, ∑ i : Fin 6, ‖B i j‖ ^ 2) ≤
        ∑ j : Fin 6, if label j = v then (1 / 4 : ℝ) else 0 :=
    Finset.sum_le_sum (fun j hj => hcol j)
  have hcard :
      (∑ j : Fin 6, if label j = v then (1 / 4 : ℝ) else 0) =
      (truthMultiplicity label v : ℝ) / 4 := by
    simp [truthMultiplicity, Finset.sum_ite, Finset.sum_const,
      nsmul_eq_mul]
    ring
  change (∑ j : Fin 6, ∑ i : Fin 6,
    ‖B i j‖ ^ 2) ≤ (truthMultiplicity label v : ℝ) / 4
  exact hsum.trans_eq hcard

/-- With the two forced opposite Hamming witnesses, both opposite
truth-fibre blocks obey dimension-sensitive squared-energy budgets. -/
theorem sixLabelled_exactHamming_oppositeBlock_energyBudget
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    sixTruthFibreBlockEnergy label D 0 3 ≤
      (truthMultiplicity label 3 : ℝ) / 4 ∧
    sixTruthFibreBlockEnergy label D 1 2 ≤
      (truthMultiplicity label 2 : ℝ) / 4 := by
  obtain ⟨h03, h12⟩ :=
    sixLabelled_exactHamming_oppositeBlock_half label D hham
  exact ⟨sixTruthFibreBlockEnergy_le_inputMultiplicity_quarter
      label D 0 3 h03,
    sixTruthFibreBlockEnergy_le_inputMultiplicity_quarter
      label D 1 2 h12⟩

end Neoplatonic.LTR
