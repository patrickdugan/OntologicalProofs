import Neoplatonic.LTR.InfiniteDiracCore

/-!
# Algebraic linearity and symmetric core action of infinite Dirac blocks

The finite-support domain is a real module. A blockwise Dirac expression
with arbitrarily growing mass and scale is a linear endomorphism of this
domain. Its symmetric pairing identity holds on every finite truncation
of the infinite direct sum.

This is the algebraic operator core used in the densely defined Hilbert
operator construction. Its extension to a maximal closed domain and the
adjoint-domain calculation remain separate analytic tasks.
-/

namespace Neoplatonic.LTR

/-- A genuine real-linear map on finitely supported two-vector sequences. -/
noncomputable def coreDiracLinear (mass scale : ℕ → ℝ) :
    (ℕ →₀ (ℝ × ℝ)) →ₗ[ℝ] (ℕ →₀ (ℝ × ℝ)) where
  toFun := coreDirac mass scale
  map_add' := by
    intro z w
    ext j
    simp only [coreDirac_apply, Finsupp.add_apply]
    exact realDiracPair_add (mass j) (scale j) (z j) (w j)
  map_smul' := by
    intro r z
    ext j
    simp only [coreDirac_apply, Finsupp.smul_apply]
    exact realDiracPair_smul (mass j) (scale j) r (z j)

/-- The square of the infinite core Dirac operator is a pointwise
multiplication by m_j²+s_j². -/
theorem coreDiracLinear_square_apply (mass scale : ℕ → ℝ)
    (z : ℕ →₀ (ℝ × ℝ)) (j : ℕ) :
    coreDiracLinear mass scale (coreDiracLinear mass scale z) j =
      ((mass j)^2 + (scale j)^2) • (z j) := by
  change coreDirac mass scale (coreDirac mass scale z) j =
    ((mass j)^2 + (scale j)^2) • z j
  simp only [coreDirac_apply]
  exact realDiracPair_square (mass j) (scale j) (z j)

/-- The actual linear Dirac action is symmetric under every finite
coordinate-sum pairing. The finset may contain any two supports. -/
theorem coreDiracLinear_symmetric_finset (mass scale : ℕ → ℝ)
    (z w : ℕ →₀ (ℝ × ℝ)) (s : Finset ℕ) :
    (∑ j ∈ s, realPairing (coreDiracLinear mass scale z j) (w j)) =
      ∑ j ∈ s, realPairing (z j) (coreDiracLinear mass scale w j) := by
  apply Finset.sum_congr rfl
  intro j hj
  change realPairing (coreDirac mass scale z j) (w j) =
    realPairing (z j) (coreDirac mass scale w j)
  simp only [coreDirac_apply]
  exact realDiracPair_symmetric (mass j) (scale j) (z j) (w j)

end Neoplatonic.LTR
