import Neoplatonic.LTR.FiveDimensionalNormExtremal
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Tactic

/-!
# LTR-MAN-21: graded norm-one coordinates force a 5D zero product

MAN-20 produces an actual nonzero eigenvector of a finite-dimensional
Hermitian norm-one operator with eigenvalue +1 or -1. Under an invertible
grading involution anticommuting with that operator, MAN-14 produces a
nonzero eigenvector at the opposite sign. Both eigenvectors can be
rescaled to unit norm.

Applying this to each of two coordinate operators feeds MAN-19, which
concludes that A B = B A = 0 from the contraction inequalities and trace
identities in complex dimension five. No orthonormal basis or eigenvector
witness is assumed in the resulting theorem.

The remaining geometric obligations are to identify the actual Dirac
commutators and their grading involutions, obtain their norm bounds from
the six exact Connes distances, and transport the operator product to the
four truth-fibre support graph.
-/

namespace Neoplatonic.LTR

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Rescale a nonzero complex Hilbert eigenvector to unit norm while
retaining its eigenvalue. -/
theorem nonzeroEigenvector_exists_unitEigenvector
    (T : E →L[ℂ] E) (μ : ℂ) (w : E)
    (hwne : w ≠ 0) (hw : T w = μ • w) :
    ∃ u : E, ‖u‖ = 1 ∧ T u = μ • u := by
  let c : ℂ := ((‖w‖⁻¹ : ℝ) : ℂ)
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hwne
  refine ⟨c • w, ?_, ?_⟩
  · rw [norm_smul]
    have hc : ‖c‖ = ‖w‖⁻¹ := by
      simp [c, Real.norm_eq_abs,
        abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w))]
    rw [hc]
    exact inv_mul_cancel₀ hn
  · calc
      T (c • w) = c • T w := map_smul T c w
      _ = c • (μ • w) := by rw [hw]
      _ = μ • (c • w) := by rw [smul_comm]

/-- An involutive grading anticommuting with a norm-one selfadjoint
operator produces two unit eigenvectors with eigenvalues +1 and -1. -/
theorem gradedNormOne_exists_signedUnitEigenvectors
    (T : E →L[ℂ] E) (G : E →ₗ[ℂ] E)
    (hself : IsSelfAdjoint T)
    (hnorm : ‖T‖ = 1)
    (hG : G.comp G = LinearMap.id)
    (hanti : T.toLinearMap.comp G = -(G.comp T.toLinearMap)) :
    ∃ uplus uminus : E,
      ‖uplus‖ = 1 ∧ ‖uminus‖ = 1 ∧
      T uplus = uplus ∧ T uminus = -uminus := by
  obtain ⟨μ, w, hμ, hwne, hw⟩ :=
    normOneSelfAdjoint_exists_signedEigenvector T hself hnorm
  obtain ⟨hflip, hGwne⟩ :=
    anticommuting_involution_pairs_eigenvectors
      T.toLinearMap G hG hanti μ w (by simpa using hw) hwne
  rcases hμ with hμ | hμ
  · subst μ
    obtain ⟨uplus, huplus, hupeig⟩ :=
      nonzeroEigenvector_exists_unitEigenvector T 1 w hwne
        (by simpa using hw)
    obtain ⟨uminus, huminus, humeig⟩ :=
      nonzeroEigenvector_exists_unitEigenvector T (-1) (G w) hGwne
        (by simpa using hflip)
    exact ⟨uplus, uminus, huplus, huminus,
      by simpa using hupeig, by simpa using humeig⟩
  · subst μ
    obtain ⟨uminus, huminus, humeig⟩ :=
      nonzeroEigenvector_exists_unitEigenvector T (-1) w hwne
        (by simpa using hw)
    obtain ⟨uplus, huplus, hupeig⟩ :=
      nonzeroEigenvector_exists_unitEigenvector T 1 (G w) hGwne
        (by simpa using hflip)
    exact ⟨uplus, uminus, huplus, huminus,
      by simpa using hupeig, by simpa using humeig⟩

/-- Five-dimensional graded Hilbert-space zero-product theorem.
The extremal eigenspaces are constructed from the norm-one
hypotheses and grading symmetry, then supplied to MAN-19. -/
theorem fiveDim_gradedCoordinates_zeroProducts
    (A B : E →L[ℂ] E) (GA GB : E →ₗ[ℂ] E)
    (hDim : Module.finrank ℂ E = 5)
    (hplus : ‖A + B‖ ≤ 1) (hminus : ‖A - B‖ ≤ 1)
    (hAself : IsSelfAdjoint A) (hBself : IsSelfAdjoint B)
    (hAnorm : ‖A‖ = 1) (hBnorm : ‖B‖ = 1)
    (htrA : LinearMap.trace ℂ E A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ E B.toLinearMap = 0)
    (hGA : GA.comp GA = LinearMap.id)
    (hGB : GB.comp GB = LinearMap.id)
    (hAG : A.toLinearMap.comp GA = -(GA.comp A.toLinearMap))
    (hBG : B.toLinearMap.comp GB = -(GB.comp B.toLinearMap)) :
    A.toLinearMap * B.toLinearMap = 0 ∧
      B.toLinearMap * A.toLinearMap = 0 := by
  obtain ⟨u0, u1, hn0, hn1, hA0, hA1⟩ :=
    gradedNormOne_exists_signedUnitEigenvectors
      A GA hAself hAnorm hGA hAG
  obtain ⟨u2, u3, hn2, hn3, hB2, hB3⟩ :=
    gradedNormOne_exists_signedUnitEigenvectors
      B GB hBself hBnorm hGB hBG
  exact fiveDim_signedUnitEigenvectors_zeroProducts
    A B hDim hplus hminus hAself hBself htrA htrB
    u0 u1 u2 u3 hn0 hn1 hn2 hn3 hA0 hA1 hB2 hB3

end Neoplatonic.LTR
