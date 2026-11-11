import Neoplatonic.LTR.SixDimensionalOrthogonalHermitianNormGate
import Neoplatonic.LTR.SixDimensionalTransitionGramPositivity
import Mathlib.Tactic

/-!
# LTR-MAN-133: bistochastic three-channel norm obstruction

This finite complex 6x6 Hilbert C*-norm theorem isolates the last
purely scalar step of the saturated opposite-double Hamming no-go.

Take the shared active opposite edge H, and four Hermitian
corner-to-neutral edges E01,E32,E02,E31, with pairwise orthogonality
within each of the two coordinate decompositions. Suppose

  A = H+E01+E32,  B = H+E02+E31.

The bistochastic transition table has real nonnegative row energies
a+b=1 with the two A edges of squared operator norm a and the two
B edges of squared operator norm b. If the active edge H has norm
at most 1/2, then one of A,B has norm strictly less than one.

This contradicts the simultaneous coordinate norm-one consequence
of exact Hamming distances. The theorem can later be specialized
to actual labelled Dirac matrices using MAN-119 through MAN-132.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A bistochastic row of neutral-channel energies rules out two
unit-norm signed coordinates once their Hermitian channels are
pairwise orthogonal and the active edge is half-sized. -/
theorem sixMatrix_bistochastic_threeEdge_unitNorm_impossible
    (H E01 E32 E02 E31 A B : SixMat)
    (hH : H.IsHermitian)
    (hE01 : E01.IsHermitian)
    (hE32 : E32.IsHermitian)
    (hE02 : E02.IsHermitian)
    (hE31 : E31.IsHermitian)
    (hH01 : H * E01 = 0) (hH32 : H * E32 = 0)
    (h0132 : E01 * E32 = 0)
    (hH02 : H * E02 = 0) (hH31 : H * E31 = 0)
    (h0231 : E02 * E31 = 0)
    (hHbound : ‖H‖ ≤ (1 / 2 : ℝ))
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1)
    (h01sq : ‖E01‖ * ‖E01‖ = a)
    (h32sq : ‖E32‖ * ‖E32‖ = a)
    (h02sq : ‖E02‖ * ‖E02‖ = b)
    (h31sq : ‖E31‖ * ‖E31‖ = b)
    (hA : A = H + E01 + E32)
    (hB : B = H + E02 + E31)
    (hAunit : (1 : ℝ) ≤ ‖A‖)
    (hBunit : (1 : ℝ) ≤ ‖B‖) :
    False := by
  rcases twoTransitionNonnegative_rowHalf a b ha hb hab with hhalfA | hhalfB
  · apply sixMatrix_threeOrthogonalHermitian_unitNorm_obstruction
      H E01 E32 hH hE01 hE32 hH01 hH32 h0132 hHbound
    · rw [h01sq]
      exact hhalfA
    · rw [h32sq]
      exact hhalfA
    · rw [← hA]
      exact hAunit
  · apply sixMatrix_threeOrthogonalHermitian_unitNorm_obstruction
      H E02 E31 hH hE02 hE31 hH02 hH31 h0231 hHbound
    · rw [h02sq]
      exact hhalfB
    · rw [h31sq]
      exact hhalfB
    · rw [← hB]
      exact hBunit

end Neoplatonic.LTR
