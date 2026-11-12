import Neoplatonic.LTR.SixDimensionalOrthogonalHermitianNormGate
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-153: robust three-channel C*-norm bound for near-orthogonal edges

At exact saturation, MAN-120 says Hermitian channels with pairwise
zero products have sum norm equal to the maximum of their norms.

In the nonsaturated six-dimensional signed witness, the opposite
corner channel H can have small nonzero products with the two
neutral edges E,F, while E*F=0 remains exact. The C*-identity
and square expansion give an exact quantitative replacement:

  ||H+E+F||² <= ||H||² + max(||E||²,||F||²)
                        + 2(||H E||+||H F||).

Consequently, if ||H||<=1/2, the neutral edge squares are <=1/2+eta,
and both cross products are <=kappa, then
  ||H+E+F||² <= 3/4 + eta + 4 kappa.
When eta+4 kappa<1/4, the actual signed coordinate norm is <1.
This is the robust operator-theoretic obstruction needed for the
nonsaturated extension of MAN-135.

All statements use genuine Euclidean complex 6x6 C*-norms.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Two Hermitian matrices have a square-norm upper bound
controlled by their individual squares and cross-channel
operator product. -/
theorem sixMatrix_twoHermitian_sum_normSq_le
    (H K : SixMat) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    ‖H + K‖ * ‖H + K‖ ≤
      ‖H‖ * ‖H‖ + ‖K‖ * ‖K‖ + 2 * ‖H * K‖ := by
  have hHsq : ‖H * H‖ = ‖H‖ * ‖H‖ := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self H
    rw [hH.eq] at h
    exact h
  have hKsq : ‖K * K‖ = ‖K‖ * ‖K‖ := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self K
    rw [hK.eq] at h
    exact h
  have hKHeq : ‖K * H‖ = ‖H * K‖ := by
    have hCT : (H * K).conjTranspose = K * H := by
      rw [Matrix.conjTranspose_mul, hH.eq, hK.eq]
    calc
      ‖K * H‖ = ‖(H * K).conjTranspose‖ :=
        congrArg norm hCT.symm
      _ = ‖H * K‖ := Matrix.l2_opNorm_conjTranspose (H * K)
  have hsumHerm : (H + K).IsHermitian := hH.add hK
  have hsumSq : ‖(H + K) * (H + K)‖ =
      ‖H + K‖ * ‖H + K‖ := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self (H + K)
    rw [hsumHerm.eq] at h
    exact h
  have hExpand : (H + K) * (H + K) =
      H * H + K * K + (H * K + K * H) := by noncomm_ring
  calc
    ‖H + K‖ * ‖H + K‖ = ‖(H + K) * (H + K)‖ :=
      hsumSq.symm
    _ = ‖H * H + K * K + (H * K + K * H)‖ := by rw [hExpand]
    _ ≤ ‖H * H + K * K‖ + ‖H * K + K * H‖ :=
      norm_add_le _ _
    _ ≤ (‖H * H‖ + ‖K * K‖) +
        (‖H * K‖ + ‖K * H‖) :=
      add_le_add (norm_add_le _ _) (norm_add_le _ _)
    _ = ‖H‖ * ‖H‖ + ‖K‖ * ‖K‖ + 2 * ‖H * K‖ := by
      rw [hHsq, hKsq, hKHeq]
      ring

/-- An exactly orthogonal pair of Hermitian neutral edges has
the maximum of their squared norms. -/
theorem sixMatrix_orthogonalHermitian_edgePair_normSq_eq_max
    (E F : SixMat)
    (hE : E.IsHermitian) (hF : F.IsHermitian)
    (hEF : E * F = 0) :
    ‖E + F‖ * ‖E + F‖ =
      max ‖E‖ ‖F‖ * max ‖E‖ ‖F‖ := by
  rw [sixMatrix_orthogonalHermitian_norm_add_eq_max E F hE hF hEF]

/-- A robust C*-operator estimate for a common Hermitian
opposite corner and two exactly disjoint neutral edges. -/
theorem sixMatrix_threeChannel_perturbed_normSq_le
    (H E F : SixMat)
    (hH : H.IsHermitian) (hE : E.IsHermitian)
    (hF : F.IsHermitian)
    (hEF : E * F = 0) :
    ‖H + E + F‖ * ‖H + E + F‖ ≤
      ‖H‖ * ‖H‖ +
      max ‖E‖ ‖F‖ * max ‖E‖ ‖F‖ +
      2 * (‖H * E‖ + ‖H * F‖) := by
  have hK : (E + F).IsHermitian := hE.add hF
  have hTwo := sixMatrix_twoHermitian_sum_normSq_le
    H (E + F) hH hK
  have hKsq := sixMatrix_orthogonalHermitian_edgePair_normSq_eq_max
    E F hE hF hEF
  have hHK : ‖H * (E + F)‖ ≤ ‖H * E‖ + ‖H * F‖ := by
    rw [mul_add]
    exact norm_add_le _ _
  have hReassoc : H + E + F = H + (E + F) := by abel
  rw [hReassoc]
  rw [hKsq] at hTwo
  nlinarith

/-- A half-sized common corner and two near-half-energy edges
with small cross products force a strictly subunit coordinate
norm, whenever the perturbative budget stays below 1/4. -/
theorem sixMatrix_threeChannel_perturbed_halfEnergy_norm_lt_one
    (H E F : SixMat)
    (hH : H.IsHermitian) (hE : E.IsHermitian)
    (hF : F.IsHermitian)
    (hEF : E * F = 0)
    (hHbound : ‖H‖ ≤ (1 / 2 : ℝ))
    (eta kappa : ℝ)
    (hEbound : ‖E‖ * ‖E‖ ≤ (1 / 2 : ℝ) + eta)
    (hFbound : ‖F‖ * ‖F‖ ≤ (1 / 2 : ℝ) + eta)
    (hHE : ‖H * E‖ ≤ kappa)
    (hHF : ‖H * F‖ ≤ kappa)
    (hbudget : eta + 4 * kappa < (1 / 4 : ℝ)) :
    ‖H + E + F‖ < (1 : ℝ) := by
  have hHpos : (0 : ℝ) ≤ ‖H‖ := norm_nonneg H
  have hHsq : ‖H‖ * ‖H‖ ≤ (1 / 4 : ℝ) := by
    nlinarith
  have hKsq :
      max ‖E‖ ‖F‖ * max ‖E‖ ‖F‖ ≤
        (1 / 2 : ℝ) + eta := by
    rcases le_total ‖E‖ ‖F‖ with hle | hle
    · rw [max_eq_right hle]
      exact hFbound
    · rw [max_eq_left hle]
      exact hEbound
  have hNorm := sixMatrix_threeChannel_perturbed_normSq_le
    H E F hH hE hF hEF
  have hpositive : (0 : ℝ) ≤ ‖H + E + F‖ :=
    norm_nonneg _
  have hSqLt : ‖H + E + F‖ * ‖H + E + F‖ < (1 : ℝ) := by
    nlinarith [hNorm, hHsq, hKsq, hHE, hHF, hbudget]
  nlinarith

end Neoplatonic.LTR
