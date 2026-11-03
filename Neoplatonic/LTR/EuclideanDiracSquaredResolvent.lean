import Neoplatonic.LTR.InfiniteDiracSelfAdjoint
import Neoplatonic.LTR.HilbertResolventWeights

/-!
# Finite-block identity for the actual squared-resolvent candidate

The real Euclidean block D_j is defined through the same two-by-two
matrix used in the maximal-domain unbounded operator. This file
identifies the square of that *continuous linear map*, then proves
the algebraic inverse identity

  (I + D_j²) (w_j v) = v,
  w_j = 1 / (1 + 4^j + s_j²).

The remaining infinite-domain proof must show that the bounded
diagonal map with weights w_j has range in Dom(D²).
-/

namespace Neoplatonic.LTR

/-- The actual two-dimensional Euclidean Dirac continuous linear map
has scalar square, rather than merely its underlying matrix. -/
theorem euclideanDiracBlock_square
    (mass scale : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    euclideanDiracBlock mass scale
        (euclideanDiracBlock mass scale v) =
      (mass ^ 2 + scale ^ 2) • v := by
  have h := congrArg
    (fun A : Matrix (Fin 2) (Fin 2) ℝ =>
      (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) A) v)
    (massDirac_square mass scale)
  simpa [euclideanDiracBlock, map_mul, map_smul] using h

/-- Each squared-resolvent coefficient is the exact inverse of the
positive scalar 1 + m_j² + s_j². -/
theorem chosenSquaredResolventWeight_inverse
    (scale : ℕ → ℝ) (j : ℕ) :
    chosenSquaredResolventWeight scale j +
      chosenSquaredResolventWeight scale j *
        (((2 : ℝ) ^ j) ^ 2 + (scale j) ^ 2) = 1 := by
  have hden : 1 + ((2 : ℝ) ^ j) ^ 2 + (scale j) ^ 2 ≠ 0 := by
    positivity
  unfold chosenSquaredResolventWeight
  field_simp [hden]
  ring

/-- The compact operator's weight in block j solves the exact
squared-Dirac inverse equation on the Euclidean two-vector. -/
theorem squaredResolventWeight_block_inverse
    (scale : ℕ → ℝ) (j : ℕ)
    (v : EuclideanSpace ℝ (Fin 2)) :
    chosenSquaredResolventWeight scale j • v +
      euclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
        (euclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
          (chosenSquaredResolventWeight scale j • v)) = v := by
  calc
    _ = chosenSquaredResolventWeight scale j • v +
        chosenSquaredResolventWeight scale j •
          (euclideanDiracBlock ((2 : ℝ) ^ j) (scale j)
            (euclideanDiracBlock ((2 : ℝ) ^ j) (scale j) v)) := by
              simp only [map_smul]
    _ = chosenSquaredResolventWeight scale j • v +
        chosenSquaredResolventWeight scale j •
          ((((2 : ℝ) ^ j) ^ 2 + (scale j) ^ 2) • v) := by
            rw [euclideanDiracBlock_square]
    _ = v := by
      rw [smul_smul, ← add_smul,
        chosenSquaredResolventWeight_inverse, one_smul]

end Neoplatonic.LTR
