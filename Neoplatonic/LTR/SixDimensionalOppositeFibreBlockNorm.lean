import Neoplatonic.LTR.SixDimensionalOppositeCornerEntryBound
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Tactic

/-!
# LTR-MAN-80: whole opposite truth-fibre block contractions

The two Hamming opposite-corner witnesses from MAN-77 control
entire blocks of the original six-dimensional Hermitian Dirac
matrix, rather than just the entries estimated in MAN-79.

Let Q_u be the diagonal projection on basis positions labelled by
truth atom u. We bound its norm by 1 in the genuine Euclidean
operator norm, and show that each compressed block Q_u M Q_v is a
contraction of M.

For (u,v)=(00,11), Q_u(A+B)Q_v=2i Q_u D Q_v.
For (u,v)=(01,10), Q_u(B-A)Q_v=2i Q_u D Q_v.

Thus exact Hamming dual distances force the sharp 1/2 operator-norm
bound for the complete opposite-corner blocks. The block operates
on the full six-dimensional Euclidean space with zero entries off
the indicated truth fibres, so its norm equals the corresponding
restricted truth-fibre operator norm.

A rank-sensitive squared-coupling budget will use these block
bounds together with the known fibre multiplicities in MAN-55.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Orthogonal truth-sector projection in an arbitrary six-coordinate
diagonal representation of four truth atoms. -/
def sixTruthFibreProjection
    (label : Fin 6 → Fin 4) (u : Fin 4) : SixMat :=
  Matrix.diagonal (fun i => if label i = u then (1 : ℂ) else 0)

/-- An atomic truth-sector projection has Euclidean Hilbert
operator norm at most one. The zero-fibre case is included. -/
theorem sixTruthFibreProjection_norm_le_one
    (label : Fin 6 → Fin 4) (u : Fin 4) :
    ‖sixTruthFibreProjection label u‖ ≤ 1 := by
  change ‖Matrix.diagonal (fun i : Fin 6 =>
    if label i = u then (1 : ℂ) else 0)‖ ≤ 1
  rw [Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).2
  intro i
  by_cases hi : label i = u <;> simp [hi]

/-- The u-to-v Dirac block, including all duplicate truth-fibre
coordinates and all their interference, embedded in the full
six-dimensional Hilbert space. -/
def sixTruthFibreBlock
    (label : Fin 6 → Fin 4) (M : SixMat)
    (u v : Fin 4) : SixMat :=
  sixTruthFibreProjection label u *
    M * sixTruthFibreProjection label v

/-- The block retains exactly the matrix entries whose row and
column labels match its truth atoms. -/
theorem sixTruthFibreBlock_entry
    (label : Fin 6 → Fin 4) (M : SixMat)
    (u v : Fin 4) (i j : Fin 6) :
    sixTruthFibreBlock label M u v i j =
      if label i = u ∧ label j = v then M i j else 0 := by
  simp only [sixTruthFibreBlock, sixTruthFibreProjection,
    Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hi : label i = u <;>
    by_cases hj : label j = v <;>
      simp [hi, hj]

/-- Any truth-fibre block of a matrix is bounded in the actual
Euclidean operator norm by the ambient matrix. -/
theorem sixTruthFibreBlock_norm_le
    (label : Fin 6 → Fin 4) (M : SixMat)
    (u v : Fin 4) :
    ‖sixTruthFibreBlock label M u v‖ ≤ ‖M‖ := by
  let P := sixTruthFibreProjection label u
  let Q := sixTruthFibreProjection label v
  have hp : ‖P‖ ≤ 1 := sixTruthFibreProjection_norm_le_one label u
  have hq : ‖Q‖ ≤ 1 := sixTruthFibreProjection_norm_le_one label v
  have hfirst : ‖P * M‖ ≤ ‖M‖ := by
    calc
      ‖P * M‖ ≤ ‖P‖ * ‖M‖ := Matrix.l2_opNorm_mul P M
      _ ≤ 1 * ‖M‖ :=
        mul_le_mul_of_nonneg_right hp (norm_nonneg M)
      _ = ‖M‖ := one_mul _
  have hsecond : ‖P * M * Q‖ ≤ ‖P * M‖ := by
    calc
      ‖P * M * Q‖ ≤ ‖P * M‖ * ‖Q‖ :=
        Matrix.l2_opNorm_mul (P * M) Q
      _ ≤ ‖P * M‖ * 1 :=
        mul_le_mul_of_nonneg_left hq (norm_nonneg (P * M))
      _ = ‖P * M‖ := mul_one _
  exact hsecond.trans hfirst

/-- A block retains pointwise scalar multiplication without any
assumption that its two truth fibres are one-dimensional. -/
theorem sixTruthFibreBlock_smul_of_entries
    (label : Fin 6 → Fin 4) (M N : SixMat)
    (u v : Fin 4) (c : ℂ)
    (h : ∀ i j : Fin 6,
      label i = u → label j = v → M i j = c * N i j) :
    sixTruthFibreBlock label M u v =
      c • sixTruthFibreBlock label N u v := by
  ext i j
  rw [sixTruthFibreBlock_entry, Matrix.smul_apply,
    sixTruthFibreBlock_entry]
  by_cases hi : label i = u
  · by_cases hj : label j = v
    · simp [hi, hj, h i j hi hj, smul_eq_mul]
    · simp [hi, hj, smul_eq_mul]
  · simp [hi, smul_eq_mul]

/-- On the entire 00→11 block, the sum-witness coordinate
commutator is exactly twice i times the original Dirac block. -/
theorem sixLabelled_sumWitness_opposite03_block
    (label : Fin 6 → Fin 4) (D : SixMat) :
    sixTruthFibreBlock label
      (labelledSquareA label D + labelledSquareB label D) 0 3 =
      ((2 : ℂ) * Complex.I) • sixTruthFibreBlock label D 0 3 := by
  apply sixTruthFibreBlock_smul_of_entries
  intro i j hi hj
  exact sixLabelled_sumWitness_opposite03_entry label D i j hi hj

/-- On the entire 01→10 block, the difference-witness
commutator is twice i times that original Dirac block. -/
theorem sixLabelled_differenceWitness_opposite12_block
    (label : Fin 6 → Fin 4) (D : SixMat) :
    sixTruthFibreBlock label
      (labelledSquareB label D - labelledSquareA label D) 1 2 =
      ((2 : ℂ) * Complex.I) • sixTruthFibreBlock label D 1 2 := by
  apply sixTruthFibreBlock_smul_of_entries
  intro i j hi hj
  exact sixLabelled_differenceWitness_opposite12_entry label D i j hi hj

/-- Unit admissibility of the 00→11 Hamming witness controls the
operator norm of the WHOLE opposite-corner block by one half. -/
theorem sixLabelled_opposite03_block_half
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsum : ‖sixLabelledDiracComm label D
      twoBitOppositeCornerSum‖ ≤ 1) :
    ‖sixTruthFibreBlock label D 0 3‖ ≤ (1 / 2 : ℝ) := by
  have hw :
      ‖(labelledSquareA label D + labelledSquareB label D : SixMat)‖ ≤ 1 := by
    change ‖(labelledSquareA label D + labelledSquareB label D
      ).toEuclideanLin.toContinuousLinearMap‖ ≤ 1
    rw [sixLabelled_sumWitness_matrix, sixLabelled_imaginaryOperator_norm]
    exact hsum
  have hb := (sixTruthFibreBlock_norm_le label
    (labelledSquareA label D + labelledSquareB label D) 0 3).trans hw
  rw [sixLabelled_sumWitness_opposite03_block, norm_smul] at hb
  have ht : ‖(2 : ℂ) * Complex.I‖ = 2 := by norm_num
  rw [ht] at hb
  linarith

/-- Unit admissibility of the 01→10 witness controls that entire
opposite-corner Dirac block, also by one half. -/
theorem sixLabelled_opposite12_block_half
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hdiff : ‖sixLabelledDiracComm label D
      twoBitOppositeCornerDifference‖ ≤ 1) :
    ‖sixTruthFibreBlock label D 1 2‖ ≤ (1 / 2 : ℝ) := by
  have hw :
      ‖(labelledSquareB label D - labelledSquareA label D : SixMat)‖ ≤ 1 := by
    change ‖(labelledSquareB label D - labelledSquareA label D
      ).toEuclideanLin.toContinuousLinearMap‖ ≤ 1
    rw [sixLabelled_differenceWitness_matrix, sixLabelled_imaginaryOperator_norm]
    exact hdiff
  have hb := (sixTruthFibreBlock_norm_le label
    (labelledSquareB label D - labelledSquareA label D) 1 2).trans hw
  rw [sixLabelled_differenceWitness_opposite12_block, norm_smul] at hb
  have ht : ‖(2 : ℂ) * Complex.I‖ = 2 := by norm_num
  rw [ht] at hb
  linarith

/-- All six exact labelled Hamming Connes distances imply two
full-block 1/2 operator-norm inequalities simultaneously. -/
theorem sixLabelled_exactHamming_oppositeBlock_half
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    ‖sixTruthFibreBlock label D 0 3‖ ≤ (1 / 2 : ℝ) ∧
    ‖sixTruthFibreBlock label D 1 2‖ ≤ (1 / 2 : ℝ) := by
  obtain ⟨hsum, hdiff⟩ :=
    sixLabelled_fullHamming_force_witnesses label D hham
  exact ⟨sixLabelled_opposite03_block_half label D hsum,
    sixLabelled_opposite12_block_half label D hdiff⟩

end Neoplatonic.LTR
