import Neoplatonic.LTR.SixDimensionalOffDiagonalNeutralEdgeOrthogonality
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-149: perturbative orthogonality of actual-sized neutral edges

MAN-123 used exact XY=0 to establish pairwise orthogonality of
the three signed Hamming witness edge components at saturation.
Away from saturation, MAN-140/147 give a small but nonzero XY.

If the off-diagonal corner X connects two orthogonal projectors
P and R, and Y lands in their sum, then exactly
  XPY = RXY, XRY = PXY.
Thus each projected corner-neutral interaction has norm bounded
by ||XY||. An individual Hermitian undirected edge E(P,N,Y)
has XE=(XPY)N if XN=0, so also ||XE||<=||XY|| for contraction N.

The two disjoint adjacent edges E(P,N,Y),E(R,M,Y) remain exactly
product-zero by their distinct support, independent of saturation.

No spectrum, basis, multiplicity or Pauli-endpoint assumption is
needed for these general complex 6x6 C*-norm identities.
-/

namespace Neoplatonic.LTR

open scoped Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A two-fibre off-diagonal corner splits the cross-channel
product XY exactly into opposite-fibre components, even when
XY itself is nonzero. -/
theorem sixMatrix_offdiagonal_XY_split_exact
    (P R X Y : SixMat)
    (hP : P * P = P) (hR : R * R = R)
    (hPR : P * R = 0) (hRP : R * P = 0)
    (hXoff : X = P * X * R + R * X * P)
    (hYrange : (P + R) * Y = Y) :
    X * P * Y = R * (X * Y) ∧
      X * R * Y = P * (X * Y) := by
  have hXP : X * P = R * X * P := by
    calc
      X * P = (P * X * R + R * X * P) * P :=
        congrArg (fun Z : SixMat => Z * P) hXoff
      _ = P * X * (R * P) + R * X * (P * P) := by noncomm_ring
      _ = R * X * P := by rw [hRP, hP]; simp
  have hXR : X * R = P * X * R := by
    calc
      X * R = (P * X * R + R * X * P) * R :=
        congrArg (fun Z : SixMat => Z * R) hXoff
      _ = P * X * (R * R) + R * X * (P * R) := by noncomm_ring
      _ = P * X * R := by rw [hR, hPR]; simp
  have hRXR : R * X * R = 0 := by
    calc
      R * X * R = R * (P * X * R + R * X * P) * R :=
        congrArg (fun Z : SixMat => R * Z * R) hXoff
      _ = (R * P) * X * (R * R) + (R * R) * X * (P * R) := by
        noncomm_ring
      _ = 0 := by rw [hRP, hR, hPR]; simp
  have hPXP : P * X * P = 0 := by
    calc
      P * X * P = P * (P * X * R + R * X * P) * P :=
        congrArg (fun Z : SixMat => P * Z * P) hXoff
      _ = (P * P) * X * (R * P) + (P * R) * X * (P * P) := by
        noncomm_ring
      _ = 0 := by rw [hP, hRP, hPR]; simp
  have hRXY : R * (X * Y) = X * P * Y := by
    calc
      R * (X * Y) = R * X * ((P + R) * Y) := by
        rw [hYrange]
        noncomm_ring
      _ = (R * X * P) * Y + (R * X * R) * Y := by noncomm_ring
      _ = X * P * Y := by
        rw [hRXR]
        simp only [zero_mul, add_zero, ← hXP]
  have hPXY : P * (X * Y) = X * R * Y := by
    calc
      P * (X * Y) = P * X * ((P + R) * Y) := by
        rw [hYrange]
        noncomm_ring
      _ = (P * X * P) * Y + (P * X * R) * Y := by noncomm_ring
      _ = X * R * Y := by
        rw [hPXP]
        simp only [zero_mul, zero_add, ← hXR]
  exact ⟨hRXY.symm, hPXY.symm⟩

/-- The opposite projection contractions preserve the upper
bound on the total cross-channel product XY. -/
theorem sixMatrix_offdiagonal_XY_split_norm_le
    (P R X Y : SixMat) (κ : ℝ)
    (hP : P * P = P) (hR : R * R = R)
    (hPR : P * R = 0) (hRP : R * P = 0)
    (hXoff : X = P * X * R + R * X * P)
    (hYrange : (P + R) * Y = Y)
    (hPnorm : ‖P‖ ≤ (1 : ℝ))
    (hRnorm : ‖R‖ ≤ (1 : ℝ))
    (hκ : 0 ≤ κ)
    (hXY : ‖X * Y‖ ≤ κ) :
    ‖X * P * Y‖ ≤ κ ∧ ‖X * R * Y‖ ≤ κ := by
  obtain ⟨hFirst, hSecond⟩ :=
    sixMatrix_offdiagonal_XY_split_exact
      P R X Y hP hR hPR hRP hXoff hYrange
  constructor
  · rw [hFirst]
    calc
      ‖R * (X * Y)‖ ≤ ‖R‖ * ‖X * Y‖ :=
        Matrix.l2_opNorm_mul R (X * Y)
      _ ≤ (1 : ℝ) * κ :=
        mul_le_mul hRnorm hXY (norm_nonneg (X * Y))
          (by norm_num)
      _ = κ := one_mul _
  · rw [hSecond]
    calc
      ‖P * (X * Y)‖ ≤ ‖P‖ * ‖X * Y‖ :=
        Matrix.l2_opNorm_mul P (X * Y)
      _ ≤ (1 : ℝ) * κ :=
        mul_le_mul hPnorm hXY (norm_nonneg (X * Y))
          (by norm_num)
      _ = κ := one_mul _

/-- If X has no neutral input column, its product with a whole
undirected edge is just a projected piece of XY followed by N. -/
theorem sixMatrix_neutralUndirectedEdge_X_product_eq
    (P N X Y : SixMat)
    (hXN : X * N = 0) :
    X * sixMatrix_neutralUndirectedEdge P N Y =
      (X * P * Y) * N := by
  change X * (P * Y * N + N * Y.conjTranspose * P) =
    (X * P * Y) * N
  calc
    X * (P * Y * N + N * Y.conjTranspose * P) =
      (X * P * Y) * N + (X * N) * Y.conjTranspose * P := by
        noncomm_ring
    _ = (X * P * Y) * N := by rw [hXN]; simp

/-- An individual genuine Hermitian corner-neutral edge is at
most as nonorthogonal to X as the total cross-channel product. -/
theorem sixMatrix_neutralUndirectedEdge_X_norm_le
    (P N X Y : SixMat) (κ : ℝ)
    (hXN : X * N = 0)
    (hNnorm : ‖N‖ ≤ (1 : ℝ))
    (hκ : 0 ≤ κ)
    (hXPY : ‖X * P * Y‖ ≤ κ) :
    ‖X * sixMatrix_neutralUndirectedEdge P N Y‖ ≤ κ := by
  rw [sixMatrix_neutralUndirectedEdge_X_product_eq P N X Y hXN]
  calc
    ‖(X * P * Y) * N‖ ≤ ‖X * P * Y‖ * ‖N‖ :=
      Matrix.l2_opNorm_mul (X * P * Y) N
    _ ≤ κ * (1 : ℝ) :=
      mul_le_mul hXPY hNnorm (norm_nonneg N) hκ
    _ = κ := mul_one _

/-- The two actual-sized directed transitions in opposite corner
and neutral fibres have small X-products, while the two
undirected edges still have EXACT zero mutual product. -/
theorem sixMatrix_offdiagonal_threeEdge_approxOrthogonal
    (P R N M X Y : SixMat) (κ : ℝ)
    (hP : P * P = P) (hR : R * R = R)
    (hPR : P * R = 0) (hRP : R * P = 0)
    (hXoff : X = P * X * R + R * X * P)
    (hYrange : (P + R) * Y = Y)
    (hPnorm : ‖P‖ ≤ (1 : ℝ))
    (hRnorm : ‖R‖ ≤ (1 : ℝ))
    (hNnorm : ‖N‖ ≤ (1 : ℝ))
    (hMnorm : ‖M‖ ≤ (1 : ℝ))
    (hXN : X * N = 0) (hXM : X * M = 0)
    (hNR : N * R = 0) (hNM : N * M = 0)
    (hPM : P * M = 0)
    (hκ : 0 ≤ κ)
    (hXY : ‖X * Y‖ ≤ κ) :
    ‖X * sixMatrix_neutralUndirectedEdge P N Y‖ ≤ κ ∧
    ‖X * sixMatrix_neutralUndirectedEdge R M Y‖ ≤ κ ∧
    sixMatrix_neutralUndirectedEdge P N Y *
      sixMatrix_neutralUndirectedEdge R M Y = 0 := by
  obtain ⟨hXPY, hXRY⟩ :=
    sixMatrix_offdiagonal_XY_split_norm_le
      P R X Y κ hP hR hPR hRP hXoff hYrange
      hPnorm hRnorm hκ hXY
  exact ⟨sixMatrix_neutralUndirectedEdge_X_norm_le
      P N X Y κ hXN hNnorm hκ hXPY,
    sixMatrix_neutralUndirectedEdge_X_norm_le
      R M X Y κ hXM hMnorm hκ hXRY,
    sixMatrix_disjointNeutralEdges_product_zero
      P R N M Y hNR hNM hPR hPM⟩

end Neoplatonic.LTR
