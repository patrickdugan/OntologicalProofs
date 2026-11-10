import Neoplatonic.LTR.SixDimensionalOppositeCornerPauliBudget
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-79: sharp opposite-corner entry bounds from Hamming witnesses

The two exact opposite-corner witnesses have Hilbert Dirac-commutator
norm at most one. The first carries each opposite 00↔11 Dirac entry
with coefficient 2i, while the second carries every 01↔10 entry
with coefficient 2i (up to sign).

A matrix entry is bounded by the genuine Euclidean Hilbert operator
norm. Hence the original Hermitian Dirac entries between opposite
truth atoms obey an explicit half-unit bound in complex modulus.

The bound is a necessary condition. It does not force the individual
opposite-corner couplings to vanish, and it is independent of the
MAN-78 cancellation between opposite-corner quadratic energies.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The magnitude of a single complex matrix entry is bounded by
the true Euclidean Hilbert operator norm of its matrix operator. -/
theorem sixMatrix_entryNorm_le_operatorNorm
    (M : SixMat) (i j : Fin 6) :
    ‖M i j‖ ≤ ‖M.toEuclideanLin.toContinuousLinearMap‖ := by
  let e : SixH := PiLp.single (2 : ℝ≥0∞) j (1 : ℂ)
  have he : ‖e‖ = 1 := by simp [e]
  have heval :
      (M.toEuclideanLin.toContinuousLinearMap e) i = M i j := by
    change (((Matrix.toEuclideanCLM (n := Fin 6) (𝕜 := ℂ)) M)
      (toLp 2 (Pi.single j (1 : ℂ)))) i = M i j
    rw [Matrix.toEuclideanCLM_toLp]
    simp [Matrix.mulVec_single_one]
  calc
    ‖M i j‖ = ‖(M.toEuclideanLin.toContinuousLinearMap e) i‖ := by rw [heval]
    _ ≤ ‖M.toEuclideanLin.toContinuousLinearMap e‖ :=
      PiLp.norm_apply_le _ i
    _ ≤ ‖M.toEuclideanLin.toContinuousLinearMap‖ * ‖e‖ :=
      (M.toEuclideanLin.toContinuousLinearMap).le_opNorm e
    _ = ‖M.toEuclideanLin.toContinuousLinearMap‖ := by rw [he, mul_one]

/-- The 00-to-11 Dirac entry appears with doubled magnitude in
the positive Hamming witness commutator. -/
theorem sixLabelled_sumWitness_opposite03_entry
    (label : Fin 6 → Fin 4) (D : SixMat)
    (i j : Fin 6) (hi : label i = 0) (hj : label j = 3) :
    (labelledSquareA label D + labelledSquareB label D) i j =
      (2 : ℂ) * Complex.I * D i j := by
  simp [Matrix.add_apply, labelledSquareA, labelledSquareB,
    squareTruthBitP, squareTruthBitQ, hi, hj]
  ring

/-- The 01-to-10 Dirac entry has doubled magnitude in
the other opposite Hamming witness commutator. -/
theorem sixLabelled_differenceWitness_opposite12_entry
    (label : Fin 6 → Fin 4) (D : SixMat)
    (i j : Fin 6) (hi : label i = 1) (hj : label j = 2) :
    (labelledSquareB label D - labelledSquareA label D) i j =
      (2 : ℂ) * Complex.I * D i j := by
  simp [Matrix.sub_apply, labelledSquareA, labelledSquareB,
    squareTruthBitP, squareTruthBitQ, hi, hj]
  ring

/-- The positive witness's unit contraction gives a universal
half-unit bound on every 00→11 Dirac entry. -/
theorem sixLabelled_opposite03_entry_half
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsum : ‖sixLabelledDiracComm label D
      twoBitOppositeCornerSum‖ ≤ 1)
    (i j : Fin 6) (hi : label i = 0) (hj : label j = 3) :
    ‖D i j‖ ≤ (1 / 2 : ℝ) := by
  have hmat :
      ‖(labelledSquareA label D + labelledSquareB label D
        ).toEuclideanLin.toContinuousLinearMap‖ ≤ 1 := by
    rw [sixLabelled_sumWitness_matrix, sixLabelled_imaginaryOperator_norm]
    exact hsum
  have h := (sixMatrix_entryNorm_le_operatorNorm
    (labelledSquareA label D + labelledSquareB label D) i j).trans hmat
  rw [sixLabelled_sumWitness_opposite03_entry label D i j hi hj] at h
  have htwo : (2 : ℝ) * ‖D i j‖ ≤ 1 := by
    simpa [norm_mul] using h
  linarith

/-- The difference witness supplies the same half-unit bound
on each oriented 01→10 Dirac coupling. -/
theorem sixLabelled_opposite12_entry_half
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hdiff : ‖sixLabelledDiracComm label D
      twoBitOppositeCornerDifference‖ ≤ 1)
    (i j : Fin 6) (hi : label i = 1) (hj : label j = 2) :
    ‖D i j‖ ≤ (1 / 2 : ℝ) := by
  have hmat :
      ‖(labelledSquareB label D - labelledSquareA label D
        ).toEuclideanLin.toContinuousLinearMap‖ ≤ 1 := by
    rw [sixLabelled_differenceWitness_matrix,
      sixLabelled_imaginaryOperator_norm]
    exact hdiff
  have h := (sixMatrix_entryNorm_le_operatorNorm
    (labelledSquareB label D - labelledSquareA label D) i j).trans hmat
  rw [sixLabelled_differenceWitness_opposite12_entry label D i j hi hj] at h
  have htwo : (2 : ℝ) * ‖D i j‖ ≤ 1 := by
    simpa [norm_mul] using h
  linarith

/-- Six exact Hamming Connes dual distances force every opposite
truth-corner entry of the *same Hermitian Dirac matrix*, in either
orientation, to have complex magnitude at most one half. -/
theorem sixLabelled_exactHamming_oppositeEntry_half
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (i j : Fin 6)
    (hopp : squareTruthOpposite (label i) (label j)) :
    ‖D i j‖ ≤ (1 / 2 : ℝ) := by
  obtain ⟨hsum, hdiff⟩ :=
    sixLabelled_fullHamming_force_witnesses label D hham
  rcases hopp with ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩ | ⟨hi, hj⟩
  · exact sixLabelled_opposite03_entry_half label D hsum i j hi hj
  · rw [hD i j, norm_star]
    exact sixLabelled_opposite03_entry_half label D hsum j i hj hi
  · exact sixLabelled_opposite12_entry_half label D hdiff i j hi hj
  · rw [hD i j, norm_star]
    exact sixLabelled_opposite12_entry_half label D hdiff j i hj hi

end Neoplatonic.LTR
