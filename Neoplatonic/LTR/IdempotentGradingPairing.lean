import Neoplatonic.LTR.TwoDirectionExtremalEigenspaces
import Mathlib.Tactic.NoncommRing

/-!
# LTR-MAN-14: grading symmetry and paired commutator eigenvalues

Every idempotent P gives an involutive grading G = 2P - 1.
For any D in an associative (possibly noncommutative) ring,
the commutator C = DP - PD anticommutes with that grading:

  G C = - C G.

This explains the ± spectral pairing of coordinate commutators.
No self-adjointness is needed for the purely algebraic identities.

For endomorphisms of a complex vector space, a map A
anticommuting with a linear involution G sends every eigenvector
of A at eigenvalue λ to a nonzero eigenvector at -λ, provided
the starting eigenvector is nonzero.

Together with LTR-MAN-13 this supports the next finite-dimensional
proof obligation: each norm-one self-adjoint coordinate commutator
has at least a two-dimensional extremal ±1 eigenspace.
-/

namespace Neoplatonic.LTR

/-- An idempotent P determines the involution 2P-1 in any ring. -/
theorem idempotent_grading_square_one
    {R : Type*} [Ring R] (p : R) (hp : p * p = p) :
    (2 * p - 1) * (2 * p - 1) = 1 := by
  calc
    (2 * p - 1) * (2 * p - 1) =
        4 * (p * p) - 4 * p + 1 := by noncomm_ring
    _ = 1 := by rw [hp]; noncomm_ring

/-- The commutator DP-PD anticommutes with the grading 2P-1,
for every idempotent P in an arbitrary (possibly noncommutative) ring. -/
theorem idempotent_grading_commutator_anticommutes
    {R : Type*} [Ring R] (d p : R) (hp : p * p = p) :
    (2 * p - 1) * (d * p - p * d) =
      -((d * p - p * d) * (2 * p - 1)) := by
  calc
    (2 * p - 1) * (d * p - p * d) =
        -((d * p - p * d) * (2 * p - 1)) +
          2 * (d * (p * p - p) - (p * p - p) * d) := by
            noncomm_ring
    _ = -((d * p - p * d) * (2 * p - 1)) := by
      simp [hp]

/-- The symmetric orientation of the same anticommutation identity. -/
theorem idempotent_commutator_grading_anticommutes
    {R : Type*} [Ring R] (d p : R) (hp : p * p = p) :
    (d * p - p * d) * (2 * p - 1) =
      -((2 * p - 1) * (d * p - p * d)) := by
  have h := idempotent_grading_commutator_anticommutes d p hp
  rw [h]
  simp

/-- In a linear involution, an anticommuting operator sends an
eigenvector at λ to an eigenvector at -λ. -/
theorem anticommuting_endomorphism_flips_eigenvector
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A G : E →ₗ[ℂ] E)
    (hanti : A.comp G = -(G.comp A))
    (λ : ℂ) (v : E) (hv : A v = λ • v) :
    A (G v) = (-λ) • (G v) := by
  have h := congrArg (fun T : E →ₗ[ℂ] E => T v) hanti
  change A (G v) = -(G (A v)) at h
  rw [hv, map_smul, neg_smul] at h
  exact h

/-- An involution maps nonzero vectors to nonzero vectors. -/
theorem linearInvolution_map_ne_zero
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (G : E →ₗ[ℂ] E)
    (hG : G.comp G = LinearMap.id)
    (v : E) (hv : v ≠ 0) :
    G v ≠ 0 := by
  intro hzero
  have h := congrArg (fun T : E →ₗ[ℂ] E => T v) hG
  change G (G v) = v at h
  rw [hzero, map_zero] at h
  exact hv h.symm

/-- The involution produces a genuine nonzero eigenvector at -λ,
so eigenvalues of an anticommuting endomorphism occur in opposite pairs. -/
theorem anticommuting_involution_pairs_eigenvectors
    {E : Type*} [AddCommGroup E] [Module ℂ E]
    (A G : E →ₗ[ℂ] E)
    (hG : G.comp G = LinearMap.id)
    (hanti : A.comp G = -(G.comp A))
    (λ : ℂ) (v : E)
    (hv : A v = λ • v) (hvne : v ≠ 0) :
    A (G v) = (-λ) • (G v) ∧ G v ≠ 0 := by
  exact ⟨anticommuting_endomorphism_flips_eigenvector
      A G hanti λ v hv,
    linearInvolution_map_ne_zero G hG v hvne⟩

end Neoplatonic.LTR
