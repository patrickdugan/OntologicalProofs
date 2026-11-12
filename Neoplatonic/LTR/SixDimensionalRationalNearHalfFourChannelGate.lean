import Neoplatonic.LTR.SixDimensionalApproxBistochasticFourChannelGate
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-166: rational quantitative four-channel obstruction

Set epsilon=1/250 and delta=9/100. The fourth-channel
hypothesis ||J||²<=2epsilon implies ||J||<=delta because
2/250 < (9/100)².

The actual near-half transition budgets of MAN-165 become
  rows <= 1+6/250, columns >= 1-2/250.
The corner-neutral bound of MAN-150, scaled by the common half
corner of MAN-132, is kappa=1/250.

MAN-163's strict numeric gate is certified by rational arithmetic:
  3*(6/250)/2 + 2/250 + 4/250 + 2*(9/100)
        + (9/100)^2 = 2481/10000 < 1/4.

This module packages the reusable matrix argument before the
following original-coordinate Dirac specialization.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A square-norm bound of 2/250 on the fourth edge yields
the rational 9/100 operator norm budget. -/
theorem sixMatrix_fourthEdge_twoOver250_norm_le_nineOver100
    (J : SixMat)
    (hSq : ‖J‖ * ‖J‖ ≤ (2 / 250 : ℝ)) :
    ‖J‖ ≤ (9 / 100 : ℝ) := by
  have hSquare : ‖J‖ ^ 2 ≤ (9 / 100 : ℝ) ^ 2 := by
    nlinarith
  exact (sq_le_sq₀ (norm_nonneg J)
    (by norm_num : (0 : ℝ) ≤ 9 / 100)).mp hSquare

/-- A rational three-parameter specialization of MAN-163:
the true four-channel norm cannot coexist with both coordinate
unit lower bounds when the row/column, cross-product, and fourth
edge error budgets are at the fixed 1/250 Pauli window. -/
theorem sixMatrix_approxBistochastic_fourChannel_oneOver250_impossible
    (H E01 E32 E02 E31 J A B : SixMat)
    (hH : H.IsHermitian)
    (hE01 : E01.IsHermitian)
    (hE32 : E32.IsHermitian)
    (hE02 : E02.IsHermitian)
    (hE31 : E31.IsHermitian)
    (h0132 : E01 * E32 = 0)
    (h0231 : E02 * E31 = 0)
    (hHbound : ‖H‖ ≤ (1 / 2 : ℝ))
    (hHE01 : ‖H * E01‖ ≤ (1 / 250 : ℝ))
    (hHE32 : ‖H * E32‖ ≤ (1 / 250 : ℝ))
    (hHE02 : ‖H * E02‖ ≤ (1 / 250 : ℝ))
    (hHE31 : ‖H * E31‖ ≤ (1 / 250 : ℝ))
    (hJSq : ‖J‖ * ‖J‖ ≤ (2 / 250 : ℝ))
    (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h01sq : ‖E01‖ * ‖E01‖ = a)
    (h32sq : ‖E32‖ * ‖E32‖ = d)
    (h02sq : ‖E02‖ * ‖E02‖ = b)
    (h31sq : ‖E31‖ * ‖E31‖ = c)
    (hrow0 : a + b ≤ 1 + 6 / 250)
    (hrow1 : c + d ≤ 1 + 6 / 250)
    (hcol0 : 1 - 2 / 250 ≤ a + c)
    (hcol1 : 1 - 2 / 250 ≤ b + d)
    (hA : A = H + E01 + E32 + J)
    (hB : B = H + E02 + E31 - J)
    (hAunit : (1 : ℝ) ≤ ‖A‖)
    (hBunit : (1 : ℝ) ≤ ‖B‖) :
    False := by
  have hJ : ‖J‖ ≤ (9 / 100 : ℝ) :=
    sixMatrix_fourthEdge_twoOver250_norm_le_nineOver100 J hJSq
  have hdelta : (0 : ℝ) ≤ 9 / 100 := by norm_num
  have hBudget :
      (3 * (6 / 250 : ℝ) / 2 + (2 / 250 : ℝ)) +
        4 * (1 / 250 : ℝ) +
        2 * (9 / 100 : ℝ) + (9 / 100 : ℝ) * (9 / 100 : ℝ) <
          (1 / 4 : ℝ) := by
    norm_num
  exact sixMatrix_approxBistochastic_fourChannel_unitNorm_impossible
    H E01 E32 E02 E31 J A B
    hH hE01 hE32 hE02 hE31
    h0132 h0231 hHbound
    (6 / 250) (2 / 250) (1 / 250) (9 / 100)
    hdelta hHE01 hHE32 hHE02 hHE31 hJ
    a b c d ha hb hc hd
    h01sq h32sq h02sq h31sq
    hrow0 hrow1 hcol0 hcol1 hBudget
    hA hB hAunit hBunit

end Neoplatonic.LTR
