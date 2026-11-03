import Neoplatonic.LTR.BoundedHilbertDiagonal

/-!
# Actual squared-resolvent tails on an infinite Hilbert direct sum

Fix masses m_j = 2^j and arbitrary real off-diagonal scales s_j.
The squared-resolvent block of D_j is scalar with weight

    w_j = 1 / (1 + 4^j + s_j^2).

This module constructs the genuine bounded Hilbert operator with
these weights and its tail operators, using mathlib's lp.mapCLM.
Their norm is bounded by (1+4^N)^(-1). Those bounds tend to zero.

Proving that the complementary finite-cutoff operator is compact
will make the full squared resolvent compact by the previously
verified norm-closed compact-operator theorem.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Exact scalar coefficient of the j-th squared-resolvent block. -/
noncomputable def chosenSquaredResolventWeight
    (scale : ℕ → ℝ) (j : ℕ) : ℝ :=
  (1 + ((2 : ℝ)^j)^2 + (scale j)^2)⁻¹

theorem chosenSquaredResolventWeight_nonneg
    (scale : ℕ → ℝ) (j : ℕ) :
    0 ≤ chosenSquaredResolventWeight scale j := by
  unfold chosenSquaredResolventWeight
  positivity

theorem chosenSquaredResolventWeight_le_tail
    (scale : ℕ → ℝ) (j : ℕ) :
    chosenSquaredResolventWeight scale j ≤ squaredResolventTail j := by
  have h := block_squaredResolvent_le_tail (fun k => (2 : ℝ)^k)
    scale (by intro k; rfl) j
  simpa [chosenSquaredResolventWeight, one_div] using h

theorem squaredResolventTail_antitone
    {N j : ℕ} (hNj : N ≤ j) :
    squaredResolventTail j ≤ squaredResolventTail N := by
  have hpow : (4 : ℝ)^N ≤ (4 : ℝ)^j :=
    pow_le_pow_right₀ (by norm_num) hNj
  have hden : (1 : ℝ) + (4 : ℝ)^N ≤ 1 + (4 : ℝ)^j := by
    linarith
  have hinv := one_div_le_one_div_of_le
    (by positivity : (0 : ℝ) < 1 + (4 : ℝ)^N) hden
  simpa [squaredResolventTail, one_div] using hinv

/-- Cut off the first N blocks, leaving the infinite squared-resolvent tail. -/
noncomputable def chosenSquaredResolventTailWeight
    (scale : ℕ → ℝ) (N j : ℕ) : ℝ :=
  if N ≤ j then chosenSquaredResolventWeight scale j else 0

theorem chosenSquaredResolventTailWeight_abs_le
    (scale : ℕ → ℝ) (N j : ℕ) :
    |chosenSquaredResolventTailWeight scale N j| ≤
      squaredResolventTail N := by
  by_cases hNj : N ≤ j
  · simp only [chosenSquaredResolventTailWeight, if_pos hNj,
      abs_of_nonneg (chosenSquaredResolventWeight_nonneg scale j)]
    exact (chosenSquaredResolventWeight_le_tail scale j).trans
      (squaredResolventTail_antitone hNj)
  · simp [chosenSquaredResolventTailWeight, hNj,
      squaredResolventTail_nonneg N]

/-- Full squared-resolvent operator, on an actual infinite Hilbert space. -/
noncomputable def chosenSquaredResolventCLM
    (scale : ℕ → ℝ) :
    DiracBlockHilbert →L[ℝ] DiracBlockHilbert :=
  boundedBlockDiagonal (chosenSquaredResolventWeight scale) 1
    (by norm_num)
    (by
      intro j
      rw [abs_of_nonneg (chosenSquaredResolventWeight_nonneg scale j)]
      exact (chosenSquaredResolventWeight_le_tail scale j).trans
        (by
          unfold squaredResolventTail
          have hbase : (1 : ℝ) ≤ 1 + (4 : ℝ)^j := by
            have hp : 0 ≤ (4 : ℝ)^j := pow_nonneg (by norm_num) j
            linarith
          have hle := one_div_le_one_div_of_le
            (by norm_num : (0 : ℝ) < 1) hbase
          simpa [one_div] using hle))

/-- An actual bounded operator whose first N blocks vanish. -/
noncomputable def chosenSquaredResolventTailCLM
    (scale : ℕ → ℝ) (N : ℕ) :
    DiracBlockHilbert →L[ℝ] DiracBlockHilbert :=
  boundedBlockDiagonal (chosenSquaredResolventTailWeight scale N)
    (squaredResolventTail N)
    (squaredResolventTail_nonneg N)
    (chosenSquaredResolventTailWeight_abs_le scale N)

/-- Explicit operator-norm convergence rate for infinite Hilbert tails. -/
theorem chosenSquaredResolventTailCLM_norm_le
    (scale : ℕ → ℝ) (N : ℕ) :
    ‖chosenSquaredResolventTailCLM scale N‖ ≤
      squaredResolventTail N :=
  boundedBlockDiagonal_norm_le _ _ _ _

end Neoplatonic.LTR
