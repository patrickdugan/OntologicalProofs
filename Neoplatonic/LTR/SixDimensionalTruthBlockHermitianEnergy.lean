import Neoplatonic.LTR.SixDimensionalTruthBlockColumnEnergy
import Mathlib.Tactic

/-!
# LTR-MAN-82: Hermitian opposite-block symmetry and minimum-fibre energy budgets

MAN-81 controls the squared energy of a labelled six-dimensional
truth-fibre block by one quarter of the input-fibre multiplicity,
assuming its full Euclidean Hilbert operator norm is at most 1/2.

For a Hermitian Dirac operator, reversing the source and target
truth atoms conjugate-transposes the entire block. This preserves
both its Hilbert operator norm and the sum of all squared entry
norms. Applying MAN-81 in both orientations therefore gives the
sharp dimension-sensitive bound by the *smaller* of the source and
target truth-fibre multiplicities.

Under all six exact complex Connes dual Hamming distances, this
applies simultaneously to 00--11 and 01--10. The subsequent
six-dimensional pattern analysis specializes the resulting bounds
to the faithful multiplicity partitions from MAN-55.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Reversing a truth-fibre Dirac block conjugate-transposes it
when the underlying Dirac matrix is Hermitian. -/
theorem sixTruthFibreBlock_conjTranspose
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (u v : Fin 4) :
    (sixTruthFibreBlock label D u v).conjTranspose =
      sixTruthFibreBlock label D v u := by
  ext i j
  simp only [Matrix.conjTranspose_apply]
  rw [sixTruthFibreBlock_entry, sixTruthFibreBlock_entry]
  by_cases hi : label i = v
  · by_cases hj : label j = u
    · simp only [hi, hj, and_self, true_and, and_true, ↓reduceIte]
      exact (hD i j).symm
    · simp [hj]
  · simp [hi]

/-- The two orientations of a Hermitian truth-fibre block have
identical full Euclidean Hilbert operator norms. -/
theorem sixTruthFibreBlock_norm_reverse
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (u v : Fin 4) :
    ‖sixTruthFibreBlock label D u v‖ =
      ‖sixTruthFibreBlock label D v u‖ := by
  rw [← sixTruthFibreBlock_conjTranspose label D hD u v]
  exact (Matrix.l2_opNorm_conjTranspose
    (sixTruthFibreBlock label D u v)).symm

/-- Squared energy is invariant under reversing the two truth
fibres, because the full Dirac block is conjugate-transposed. -/
theorem sixTruthFibreBlockEnergy_reverse
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (u v : Fin 4) :
    sixTruthFibreBlockEnergy label D u v =
      sixTruthFibreBlockEnergy label D v u := by
  unfold sixTruthFibreBlockEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have hentry :
      sixTruthFibreBlock label D u v j i =
        star (sixTruthFibreBlock label D v u i j) := by
    have h := congrArg (fun M : SixMat => M j i)
      (sixTruthFibreBlock_conjTranspose label D hD v u)
    simpa only [Matrix.conjTranspose_apply] using h.symm
  rw [hentry, norm_star]

/-- Hermitian symmetry sharpens the full-block squared-energy bound
to the *minimum* of the input and output truth-fibre dimensions. -/
theorem sixTruthFibreBlockEnergy_le_minMultiplicity_quarter
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (u v : Fin 4)
    (hnorm : ‖sixTruthFibreBlock label D u v‖ ≤ (1 / 2 : ℝ)) :
    sixTruthFibreBlockEnergy label D u v ≤
      ((min (truthMultiplicity label u)
        (truthMultiplicity label v) : ℕ) : ℝ) / 4 := by
  have hin :=
    sixTruthFibreBlockEnergy_le_inputMultiplicity_quarter
      label D u v hnorm
  have hrevNorm :
      ‖sixTruthFibreBlock label D v u‖ ≤ (1 / 2 : ℝ) := by
    rw [← sixTruthFibreBlock_norm_reverse label D hD u v]
    exact hnorm
  have hrev :=
    sixTruthFibreBlockEnergy_le_inputMultiplicity_quarter
      label D v u hrevNorm
  have hout : sixTruthFibreBlockEnergy label D u v ≤
      (truthMultiplicity label u : ℝ) / 4 := by
    rw [sixTruthFibreBlockEnergy_reverse label D hD u v]
    exact hrev
  rcases le_total (truthMultiplicity label u) (truthMultiplicity label v)
    with hle | hle
  · rw [min_eq_left hle]
    exact hout
  · rw [min_eq_right hle]
    exact hin

/-- All six exact Hamming Connes distances constrain the two true
opposite-corner squared energies by one quarter of the *smaller*
of their two fibre multiplicities. -/
theorem sixLabelled_exactHamming_oppositeBlock_minEnergy
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    sixTruthFibreBlockEnergy label D 0 3 ≤
      ((min (truthMultiplicity label 0)
        (truthMultiplicity label 3) : ℕ) : ℝ) / 4 ∧
    sixTruthFibreBlockEnergy label D 1 2 ≤
      ((min (truthMultiplicity label 1)
        (truthMultiplicity label 2) : ℕ) : ℝ) / 4 := by
  obtain ⟨h03, h12⟩ :=
    sixLabelled_exactHamming_oppositeBlock_half label D hham
  exact ⟨sixTruthFibreBlockEnergy_le_minMultiplicity_quarter
      label D hD 0 3 h03,
    sixTruthFibreBlockEnergy_le_minMultiplicity_quarter
      label D hD 1 2 h12⟩

end Neoplatonic.LTR
