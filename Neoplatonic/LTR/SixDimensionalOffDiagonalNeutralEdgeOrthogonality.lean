import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic

/-!
# LTR-MAN-123: split the zero-product condition into genuine neutral edges

The algebraic core of the original-coordinate six-dimensional saturated
Hamming obstruction. An off-diagonal corner operator X has two orthogonal
truth-fibre output projections P and R. The corner-neutral map Y lands in
their sum. MAN-94 proves X*Y=0 for a saturated signed involution.

The first theorem upgrades X*Y=0 to X*P*Y=0 and X*R*Y=0. Thus the
active corner is orthogonal to each of the neutral-exchange output
channels individually. Undirected neutral edges entering different
corner and neutral truth fibres also have zero mutual product, from
support orthogonality alone.

These abstract complex 6x6 lemmas are intended to be instantiated in
the original labelled-Dirac chart. They do not assume a canonical U(2)
chart or prove the final Connes distance contradiction.
-/

namespace Neoplatonic.LTR

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Off-diagonal corner support and XY=0 force separate annihilation
of the two complementary output fibres of Y. -/
theorem sixMatrix_offdiagonal_XY_zero_split
    (P R X Y : SixMat)
    (hP : P * P = P) (hR : R * R = R)
    (hPR : P * R = 0) (hRP : R * P = 0)
    (hXoff : X = P * X * R + R * X * P)
    (hYrange : (P + R) * Y = Y)
    (hXY : X * Y = 0) :
    X * P * Y = 0 ∧ X * R * Y = 0 := by
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
      R * (X * Y) = R * X * ((P + R) * Y) := by rw [hYrange]; noncomm_ring
      _ = (R * X * P) * Y + (R * X * R) * Y := by noncomm_ring
      _ = X * P * Y := by rw [hRXR]; simp only [zero_mul, add_zero, ← hXP]
  have hPXY : P * (X * Y) = X * R * Y := by
    calc
      P * (X * Y) = P * X * ((P + R) * Y) := by rw [hYrange]; noncomm_ring
      _ = (P * X * P) * Y + (P * X * R) * Y := by noncomm_ring
      _ = X * R * Y := by rw [hPXP]; simp only [zero_mul, zero_add, ← hXR]
  constructor
  · calc
      X * P * Y = R * (X * Y) := hRXY.symm
      _ = 0 := by rw [hXY]; simp
  · calc
      X * R * Y = P * (X * Y) := hPXY.symm
      _ = 0 := by rw [hXY]; simp

/-- The Hermitian undirected edge associated with a corner output
projector P and a neutral input projector N. -/
def sixMatrix_neutralUndirectedEdge (P N Y : SixMat) : SixMat :=
  P * Y * N + N * Y.conjTranspose * P

/-- A neutral undirected edge is Hermitian whenever its endpoint
projections are Hermitian. -/
theorem sixMatrix_neutralUndirectedEdge_hermitian
    (P N Y : SixMat)
    (hP : P.IsHermitian) (hN : N.IsHermitian) :
    (sixMatrix_neutralUndirectedEdge P N Y).IsHermitian := by
  change (sixMatrix_neutralUndirectedEdge P N Y).conjTranspose =
    sixMatrix_neutralUndirectedEdge P N Y
  simp only [sixMatrix_neutralUndirectedEdge,
    Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    hP.eq, hN.eq, Matrix.conjTranspose_conjTranspose]
  noncomm_ring

/-- An individual corner-neutral edge is killed by X as soon as
the corresponding projected row of XY and X's neutral column vanish. -/
theorem sixMatrix_neutralUndirectedEdge_X_product_zero
    (P N X Y : SixMat)
    (hXPY : X * P * Y = 0) (hXN : X * N = 0) :
    X * sixMatrix_neutralUndirectedEdge P N Y = 0 := by
  change X * (P * Y * N + N * Y.conjTranspose * P) = 0
  calc
    X * (P * Y * N + N * Y.conjTranspose * P) =
        (X * P * Y) * N + (X * N) * Y.conjTranspose * P := by
          noncomm_ring
    _ = 0 := by rw [hXPY, hXN]; simp

/-- If the input fibres are distinct, and the output fibres are
distinct, their undirected transition edges have zero product. -/
theorem sixMatrix_disjointNeutralEdges_product_zero
    (P R N M Y : SixMat)
    (hNR : N * R = 0) (hNM : N * M = 0)
    (hPR : P * R = 0) (hPM : P * M = 0) :
    sixMatrix_neutralUndirectedEdge P N Y *
      sixMatrix_neutralUndirectedEdge R M Y = 0 := by
  change (P * Y * N + N * Y.conjTranspose * P) *
    (R * Y * M + M * Y.conjTranspose * R) = 0
  calc
    (P * Y * N + N * Y.conjTranspose * P) *
        (R * Y * M + M * Y.conjTranspose * R) =
        P * Y * (N * R) * Y * M +
        P * Y * (N * M) * Y.conjTranspose * R +
        N * Y.conjTranspose * (P * R) * Y * M +
        N * Y.conjTranspose * (P * M) * Y.conjTranspose * R := by
          noncomm_ring
    _ = 0 := by rw [hNR, hNM, hPR, hPM]; simp

/-- MAN-94's XY=0 and the opposite-corner structure discharge
the three forward product-zero goals required for MAN-120. -/
theorem sixMatrix_offdiagonal_threeEdgeProducts_zero
    (P R N M X Y : SixMat)
    (hP : P * P = P) (hR : R * R = R)
    (hPR : P * R = 0) (hRP : R * P = 0)
    (hXoff : X = P * X * R + R * X * P)
    (hYrange : (P + R) * Y = Y)
    (hXY : X * Y = 0)
    (hXN : X * N = 0) (hXM : X * M = 0)
    (hNR : N * R = 0) (hNM : N * M = 0)
    (hPM : P * M = 0) :
    X * sixMatrix_neutralUndirectedEdge P N Y = 0 ∧
    X * sixMatrix_neutralUndirectedEdge R M Y = 0 ∧
    sixMatrix_neutralUndirectedEdge P N Y *
      sixMatrix_neutralUndirectedEdge R M Y = 0 := by
  obtain ⟨hXPY, hXRY⟩ := sixMatrix_offdiagonal_XY_zero_split
    P R X Y hP hR hPR hRP hXoff hYrange hXY
  exact ⟨sixMatrix_neutralUndirectedEdge_X_product_zero P N X Y hXPY hXN,
    sixMatrix_neutralUndirectedEdge_X_product_zero R M X Y hXRY hXM,
    sixMatrix_disjointNeutralEdges_product_zero P R N M Y
      hNR hNM hPR hPM⟩

end Neoplatonic.LTR
