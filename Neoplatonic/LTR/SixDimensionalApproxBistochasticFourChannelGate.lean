import Neoplatonic.LTR.SixDimensionalPerturbedFourChannelNorm
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-163: approximate bistochastic transitions give a robust four-channel norm gate

For nonnegative transition energies

       neutral 01   neutral 10
  00       a             b
  11       c             d

assume both row sums are at most 1+rho and both column sums are at
least 1-sigma. Then the two energy pairs belonging to the two
coordinate operators obey an approximate half-energy alternative:

  (a,d <= 1/2 + 3rho/2 + sigma) or
  (b,c <= 1/2 + 3rho/2 + sigma).

This uses only additive scalar inequalities and is stable under
small non-bistochastic defects, unlike the saturated MAN-133 equality.

Compose this dichotomy with MAN-155's original-sized four-channel
C*-norm inequality. One of the coordinate commutators must have
norm strictly less than one whenever

  (3rho/2+sigma) + 4kappa + 2delta + delta² < 1/4,

where kappa bounds the corner-edge products and delta the fourth edge.

The theorem is a reusable numeric/operator bridge; the separate
original-Dirac task is to supply concrete rho and sigma from the
near-involution Gram defects of MAN-140/147/162.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A nearly bistochastic 2x2 transition table has a coordinate
pair whose two squared energies are simultaneously at most
1/2 + 3rho/2 + sigma. -/
theorem fourTransition_approxBistochastic_halfPair
    (a b c d rho sigma : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hrow0 : a + b ≤ 1 + rho)
    (hrow1 : c + d ≤ 1 + rho)
    (hcol0 : 1 - sigma ≤ a + c)
    (hcol1 : 1 - sigma ≤ b + d) :
    (a ≤ (1 / 2 : ℝ) + 3 * rho / 2 + sigma ∧
      d ≤ (1 / 2 : ℝ) + 3 * rho / 2 + sigma) ∨
    (b ≤ (1 / 2 : ℝ) + 3 * rho / 2 + sigma ∧
      c ≤ (1 / 2 : ℝ) + 3 * rho / 2 + sigma) := by
  have had : a - d ≤ rho + sigma := by linarith
  have hda : d - a ≤ rho + sigma := by linarith
  have hbc : b - c ≤ rho + sigma := by linarith
  have hcb : c - b ≤ rho + sigma := by linarith
  by_cases haSmall : a ≤ (1 / 2 : ℝ) + rho / 2
  · left
    constructor <;> linarith
  · right
    have hbSmall : b ≤ (1 / 2 : ℝ) + rho / 2 := by
      linarith
    constructor <;> linarith

/-- Stable replacement for MAN-133's exact bistochastic
three-Hermitian-edge obstruction, now accounting for a genuinely
nonsaturated fourth opposite-neutral edge. -/
theorem sixMatrix_approxBistochastic_fourChannel_unitNorm_impossible
    (H E01 E32 E02 E31 J A B : SixMat)
    (hH : H.IsHermitian)
    (hE01 : E01.IsHermitian)
    (hE32 : E32.IsHermitian)
    (hE02 : E02.IsHermitian)
    (hE31 : E31.IsHermitian)
    (h0132 : E01 * E32 = 0)
    (h0231 : E02 * E31 = 0)
    (hHbound : ‖H‖ ≤ (1 / 2 : ℝ))
    (rho sigma kappa delta : ℝ)
    (hdelta : 0 ≤ delta)
    (hHE01 : ‖H * E01‖ ≤ kappa)
    (hHE32 : ‖H * E32‖ ≤ kappa)
    (hHE02 : ‖H * E02‖ ≤ kappa)
    (hHE31 : ‖H * E31‖ ≤ kappa)
    (hJ : ‖J‖ ≤ delta)
    (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d)
    (h01sq : ‖E01‖ * ‖E01‖ = a)
    (h32sq : ‖E32‖ * ‖E32‖ = d)
    (h02sq : ‖E02‖ * ‖E02‖ = b)
    (h31sq : ‖E31‖ * ‖E31‖ = c)
    (hrow0 : a + b ≤ 1 + rho)
    (hrow1 : c + d ≤ 1 + rho)
    (hcol0 : 1 - sigma ≤ a + c)
    (hcol1 : 1 - sigma ≤ b + d)
    (hbudget : (3 * rho / 2 + sigma) + 4 * kappa +
      2 * delta + delta * delta < (1 / 4 : ℝ))
    (hA : A = H + E01 + E32 + J)
    (hB : B = H + E02 + E31 - J)
    (hAunit : (1 : ℝ) ≤ ‖A‖)
    (hBunit : (1 : ℝ) ≤ ‖B‖) :
    False := by
  rcases fourTransition_approxBistochastic_halfPair
    a b c d rho sigma ha hb hc hd hrow0 hrow1 hcol0 hcol1
    with hHalfA | hHalfB
  · have hUnitA : (1 : ℝ) ≤ ‖H + E01 + E32 + J‖ := by
      rw [← hA]
      exact hAunit
    exact sixMatrix_fourChannel_perturbed_unitNorm_impossible
      H E01 E32 J hH hE01 hE32 h0132 hHbound
      (3 * rho / 2 + sigma) kappa delta hdelta
      (h01sq.symm ▸ hHalfA.1) (h32sq.symm ▸ hHalfA.2)
      hHE01 hHE32 hJ hbudget hUnitA
  · have hJneg : ‖-J‖ ≤ delta := by
      simpa only [norm_neg] using hJ
    have hUnitB : (1 : ℝ) ≤ ‖H + E02 + E31 + (-J)‖ := by
      have heq : H + E02 + E31 + (-J) = B := by
        rw [hB]
        abel
      rw [heq]
      exact hBunit
    exact sixMatrix_fourChannel_perturbed_unitNorm_impossible
      H E02 E31 (-J) hH hE02 hE31 h0231 hHbound
      (3 * rho / 2 + sigma) kappa delta hdelta
      (h02sq.symm ▸ hHalfB.1) (h31sq.symm ▸ hHalfB.2)
      hHE02 hHE31 hJneg hbudget hUnitB

end Neoplatonic.LTR
