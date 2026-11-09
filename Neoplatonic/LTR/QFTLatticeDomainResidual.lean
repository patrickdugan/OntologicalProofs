import Neoplatonic.LTR.QFTLatticeSchur
import Neoplatonic.LTR.ComplexOrdinaryResolventGlobal

/-!
# Domain-correct residual certificates for unbounded Dirac operators

A one-particle lattice Hamiltonian is an unbounded operator. Its finite-section
witness must therefore be inserted into the *domain* before applying H-z.
The abstract NormedRing identity in QFTLatticeSchur does not record that domain.

This file proves the residual estimate for a genuine LinearPMap on a complex
normed space and then instantiates it on the existing infinite Hilbert sum
lp (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 with the maximal Dirac domain.

The Shao--Sopenko hopping kernel and its ℓ²(ℤ) realization are separate
analytic inputs. The instance below uses the previously constructed,
block-diagonal Dirac model, as a checked demonstration of the domain API.
-/

namespace Neoplatonic.LTR

/-- Domain-valid approximate solutions admit a posteriori error bounds.
T is allowed to be unbounded; only its inverse R is assumed bounded. -/
theorem qftLattice_domain_residual_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →ₗ.[ℂ] E) (R : E →L[ℂ] E) (z : ℂ)
    (hleft : ∀ (u : E) (hu : u ∈ T.domain),
      R (T ⟨u, hu⟩ - z • u) = u)
    (f u : E) (hu : u ∈ T.domain) :
    ‖R f - u‖ ≤ ‖R‖ * ‖f - (T ⟨u, hu⟩ - z • u)‖ := by
  have hid : R (T ⟨u, hu⟩ - z • u) = u := hleft u hu
  calc
    ‖R f - u‖ = ‖R (f - (T ⟨u, hu⟩ - z • u))‖ := by
      rw [map_sub, hid]
    _ ≤ ‖R‖ * ‖f - (T ⟨u, hu⟩ - z • u)‖ := R.le_opNorm _

/-- A residual certificate and an inverse-norm bound yield a numerical
error certificate, with no reference to how the witness was generated. -/
theorem qftLattice_domain_residual_certificate
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →ₗ.[ℂ] E) (R : E →L[ℂ] E) (z : ℂ)
    (hleft : ∀ (u : E) (hu : u ∈ T.domain),
      R (T ⟨u, hu⟩ - z • u) = u)
    (f u : E) (hu : u ∈ T.domain)
    (K ε : ℝ) (hK : 0 ≤ K)
    (hR : ‖R‖ ≤ K)
    (hres : ‖f - (T ⟨u, hu⟩ - z • u)‖ ≤ ε) :
    ‖R f - u‖ ≤ K * ε := by
  calc
    ‖R f - u‖ ≤ ‖R‖ * ‖f - (T ⟨u, hu⟩ - z • u)‖ :=
      qftLattice_domain_residual_norm_le T R z hleft f u hu
    _ ≤ K * ‖f - (T ⟨u, hu⟩ - z • u)‖ :=
      mul_le_mul_of_nonneg_right hR (norm_nonneg _)
    _ ≤ K * ε := mul_le_mul_of_nonneg_left hres hK

/-- Concrete maximal-domain version on an infinite complex Hilbert space.
The chosen R is the proved inverse of (D-i) on this exact maximal domain. -/
theorem qftLattice_complexBlockDirac_residual_norm_le
    (scale : ℕ → ℝ) (f u : ComplexDiracBlockHilbert)
    (hu : u ∈ maximalComplexDiracDomain (fun j => (2 : ℝ) ^ j) scale) :
    ‖chosenComplexOrdinaryResolventCLM scale f - u‖ ≤
      ‖chosenComplexOrdinaryResolventCLM scale‖ *
        ‖f - ((maximalComplexDiracPMap (fun j => (2 : ℝ) ^ j) scale)
          ⟨u, hu⟩ - Complex.I • u)‖ := by
  let T := maximalComplexDiracPMap (fun j => (2 : ℝ) ^ j) scale
  let R := chosenComplexOrdinaryResolventCLM scale
  have hleft : ∀ (v : ComplexDiracBlockHilbert) (hv : v ∈ T.domain),
      R (T ⟨v, hv⟩ - Complex.I • v) = v := by
    intro v hv
    exact chosenComplexOrdinaryResolvent_left_inverse scale v hv
  exact qftLattice_domain_residual_norm_le T R Complex.I hleft f u hu

end Neoplatonic.LTR
