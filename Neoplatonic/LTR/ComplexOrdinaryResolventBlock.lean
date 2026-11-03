import Neoplatonic.LTR.ComplexSquaredResolventIdentity

/-!
# The ordinary complex Dirac resolvent at i: exact 2×2 inverse algebra

For each Hermitian two-point block D_j, the inverse of D_j - iI
is the continuous complex-linear map
  (D_j + iI) / (1 + 4^j + s_j²).

This file proves both inverse equations on each finite-dimensional
complex Hilbert block. Uniform bounds, direct-sum compactness and
the maximal-domain inverse are separate infinite-dimensional steps.
-/

namespace Neoplatonic.LTR

/-- Blockwise ordinary resolvent candidate at the nonreal spectral point i. -/
noncomputable def complexOrdinaryResolventBlock (scale : ℕ → ℝ) (j : ℕ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)).comp
      (complexScalarBlockCLM (chosenSquaredResolventWeight scale j)) +
    Complex.I • complexScalarBlockCLM (chosenSquaredResolventWeight scale j)

/-- Explicit action of the bounded ordinary resolvent block. -/
theorem complexOrdinaryResolventBlock_apply
    (scale : ℕ → ℝ) (j : ℕ) (v : EuclideanSpace ℂ (Fin 2)) :
    complexOrdinaryResolventBlock scale j v =
      complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
        (((chosenSquaredResolventWeight scale j : ℝ) : ℂ) • v) +
      Complex.I • (((chosenSquaredResolventWeight scale j : ℝ) : ℂ) • v) := by
  simp [complexOrdinaryResolventBlock, complexScalarBlockCLM]

/-- The ordinary resolvent is a right inverse of D_j - iI. -/
theorem complexOrdinaryResolventBlock_right_inverse
    (scale : ℕ → ℝ) (j : ℕ) (v : EuclideanSpace ℂ (Fin 2)) :
    complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
      (complexOrdinaryResolventBlock scale j v) -
      Complex.I • (complexOrdinaryResolventBlock scale j v) = v := by
  let D := complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
  let w : ℂ := ((chosenSquaredResolventWeight scale j : ℝ) : ℂ)
  have hq : complexOrdinaryResolventBlock scale j v =
      D (w • v) + Complex.I • (w • v) :=
    complexOrdinaryResolventBlock_apply scale j v
  have hI : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
  have hiw : Complex.I * (Complex.I * w) = -w := by
    rw [← mul_assoc, hI]
    simp
  have hblock : D (D (w • v)) + w • v = v := by
    simpa only [add_comm] using
      complexSquaredResolventWeight_block_inverse scale j v
  calc
    D (complexOrdinaryResolventBlock scale j v) -
        Complex.I • (complexOrdinaryResolventBlock scale j v) =
      D (D (w • v) + Complex.I • (w • v)) -
        Complex.I • (D (w • v) + Complex.I • (w • v)) := by rw [hq]
    _ = D (D (w • v)) + w • v := by
      simp only [map_add, map_smul, smul_add, smul_smul]
      rw [hiw]
      simp only [neg_smul]
      abel
    _ = v := hblock

/-- The ordinary resolvent is also a left inverse of D_j - iI. -/
theorem complexOrdinaryResolventBlock_left_inverse
    (scale : ℕ → ℝ) (j : ℕ) (v : EuclideanSpace ℂ (Fin 2)) :
    complexOrdinaryResolventBlock scale j
      (complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j) v -
        Complex.I • v) = v := by
  let D := complexEuclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
  let w : ℂ := ((chosenSquaredResolventWeight scale j : ℝ) : ℂ)
  have hI : Complex.I * Complex.I = (-1 : ℂ) := Complex.I_mul_I
  have hiw : Complex.I * (Complex.I * w) = -w := by
    rw [← mul_assoc, hI]
    simp
  have hblock : w • D (D v) + w • v = v := by
    have h := complexSquaredResolventWeight_block_inverse scale j v
    rw [map_smul, map_smul] at h
    simpa only [add_comm] using h
  rw [complexOrdinaryResolventBlock_apply]
  change D (w • (D v - Complex.I • v)) +
    Complex.I • (w • (D v - Complex.I • v)) = v
  calc
    D (w • (D v - Complex.I • v)) +
        Complex.I • (w • (D v - Complex.I • v)) =
      w • D (D v) + w • v := by
        simp only [smul_sub, map_sub, map_smul, smul_smul]
        rw [mul_comm w Complex.I, hiw]
        simp only [neg_smul]
        abel
    _ = v := hblock

end Neoplatonic.LTR
