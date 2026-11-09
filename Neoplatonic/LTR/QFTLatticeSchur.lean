import Neoplatonic.LTR.ComplexOrdinaryResolventDecay

/-!
# Schur and residual certificates for infinite-flavor lattice truncations

The Dirac flavor Hamiltonian of Shao--Sopenko (arXiv:2611.05329v1)
uses an unbounded diagonal operator and a bounded hopping operator.
This file records the *bounded algebraic* certificate-transfer steps:

* Given a left inverse, a finitely supported approximate solution has
  resolvent error bounded by the inverse norm times its full residual.
* Given a Schur-complement identity, the compressed-resolvent error is
  bounded by a product of the five operator norms.

The complex Hilbert-space domain and infinite Fourier kernel estimates
are separate analytic premises. In particular these results should not be
advertised as a Lean formalization of the whole QFT/lattice map.
-/

namespace Neoplatonic.LTR

/-- Algebraic resolvent residual identity. It applies in any normed ring;
for the unbounded Dirac operator one first establishes the analogous
vector identity on the maximal operator domain. -/
theorem qftLattice_residual_identity
    {A : Type*} [NormedRing A]
    (R H U F : A) (hleft : R * H = 1) :
    R * F - U = R * (F - H * U) := by
  calc
    R * F - U = R * F - (R * H) * U := by rw [hleft, one_mul]
    _ = R * (F - H * U) := by rw [mul_sub, mul_assoc]

/-- The residual of any candidate bounds its error after applying the
bounded inverse, with no reliance on how the candidate was generated. -/
theorem qftLattice_residual_norm_le
    {A : Type*} [NormedRing A]
    (R H U F : A) (hleft : R * H = 1) :
    ‖R * F - U‖ ≤ ‖R‖ * ‖F - H * U‖ := by
  rw [qftLattice_residual_identity R H U F hleft]
  exact norm_mul_le _ _

/-- An exact Schur complement identity implies a product-of-norms
certificate for the compression error. -/
theorem qftLattice_schur_norm_le
    {A : Type*} [NormedRing A]
    (G R B T Badj : A)
    (hschur : G - R = (((R * B) * T) * Badj) * G) :
    ‖G - R‖ ≤ (((‖R‖ * ‖B‖) * ‖T‖) * ‖Badj‖) * ‖G‖ := by
  rw [hschur]
  calc
    ‖(((R * B) * T) * Badj) * G‖ ≤
        ‖((R * B) * T) * Badj‖ * ‖G‖ := norm_mul_le _ _
    _ ≤ (‖(R * B) * T‖ * ‖Badj‖) * ‖G‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ ≤ ((‖R * B‖ * ‖T‖) * ‖Badj‖) * ‖G‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        (norm_nonneg _)
    _ ≤ (((‖R‖ * ‖B‖) * ‖T‖) * ‖Badj‖) * ‖G‖ :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
          (norm_nonneg _))
        (norm_nonneg _)

/-- The abstract Schur rate is inherited from any proven tail bound.
The explicit Dirac coefficients are established in the companion analytic
note in MoralityLabAI/Compactification-Theory. -/
theorem qftLattice_schur_rate
    {A : Type*} [NormedRing A]
    (G R B T Badj : A) (rate : ℝ)
    (hschur : G - R = (((R * B) * T) * Badj) * G)
    (hrate : (((‖R‖ * ‖B‖) * ‖T‖) * ‖Badj‖) * ‖G‖ ≤ rate) :
    ‖G - R‖ ≤ rate :=
  (qftLattice_schur_norm_le G R B T Badj hschur).trans hrate

end Neoplatonic.LTR