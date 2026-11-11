import Neoplatonic.LTR.SixDimensionalActualCornerOffDiagonal
import Mathlib.Tactic

/-!
# LTR-MAN-125: the true 6D positive-saturated coordinate edges multiply to zero

MAN-124 certifies X P0 Y = X P3 Y = 0 for the genuine positive
signed Hamming witness W=A+B. Each neutral fibre N1,N2 is
orthogonal to both opposite corner fibres P0,P3, and the actual
corner X=CWC consequently satisfies X Nv=0.

Using MAN-123's neutral undirected edge E(P,N)=PYN+NYᴴP,
the original labelled Dirac witness therefore has the six
product-zero identities needed by MAN-120:

  X E02 = X E31 = E02 E31 = 0,
  X E01 = X E32 = E01 E32 = 0.

The first triple is associated with the A-coordinate edges and
the second with the B-coordinate edges of MAN-121. This theorem
uses no canonical U(2) chart. The norm and edge-identification
bridges remain separate formal obligations.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Distinct truth fibres give orthogonal diagonal projectors
in any faithful or nonfaithful six-coordinate labelling. -/
theorem sixTruthFibreProjection_mul_zero_of_distinct
    (label : Fin 6 → Fin 4) (u v : Fin 4) (h : u ≠ v) :
    sixTruthFibreProjection label u *
      sixTruthFibreProjection label v = 0 := by
  ext i j
  simp only [sixTruthFibreProjection, Matrix.diagonal_mul,
    Matrix.diagonal_apply]
  by_cases hi : label i = u
  · have hiv : label i ≠ v := by simpa [hi] using h
    simp [hi, hiv]
  · simp [hi]

/-- Under genuine positive saturation, the two incident
neutral edges of either Dirac coordinate are mutually
orthogonal and separately orthogonal to the active corner X.
All six products are in the original six-dimensional chart. -/
theorem sixLabelled_exactHamming_saturated03_actual_neutralEdges_products_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    let X := C * W * C
    let Y := C * W * Q
    let P0 := sixTruthFibreProjection label 0
    let P3 := sixTruthFibreProjection label 3
    let N1 := sixTruthFibreProjection label 1
    let N2 := sixTruthFibreProjection label 2
    let E02 := sixMatrix_neutralUndirectedEdge P0 N2 Y
    let E31 := sixMatrix_neutralUndirectedEdge P3 N1 Y
    let E01 := sixMatrix_neutralUndirectedEdge P0 N1 Y
    let E32 := sixMatrix_neutralUndirectedEdge P3 N2 Y
    X * E02 = 0 ∧ X * E31 = 0 ∧ E02 * E31 = 0 ∧
    X * E01 = 0 ∧ X * E32 = 0 ∧ E01 * E32 = 0 := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let X : SixMat := C * W * C
  let Y : SixMat := C * W * Q
  let P0 : SixMat := sixTruthFibreProjection label 0
  let P3 : SixMat := sixTruthFibreProjection label 3
  let N1 : SixMat := sixTruthFibreProjection label 1
  let N2 : SixMat := sixTruthFibreProjection label 2
  change
    X * sixMatrix_neutralUndirectedEdge P0 N2 Y = 0 ∧
    X * sixMatrix_neutralUndirectedEdge P3 N1 Y = 0 ∧
    sixMatrix_neutralUndirectedEdge P0 N2 Y *
      sixMatrix_neutralUndirectedEdge P3 N1 Y = 0 ∧
    X * sixMatrix_neutralUndirectedEdge P0 N1 Y = 0 ∧
    X * sixMatrix_neutralUndirectedEdge P3 N2 Y = 0 ∧
    sixMatrix_neutralUndirectedEdge P0 N1 Y *
      sixMatrix_neutralUndirectedEdge P3 N2 Y = 0
  have hRows :=
    sixLabelled_exactHamming_saturated03_actualCorner_twoRows_zero
      label D hD hham h03 h12
  change X * P0 * Y = 0 ∧ X * P3 * Y = 0 at hRows
  obtain ⟨hXP0Y, hXP3Y⟩ := hRows
  have hC : C = P0 + P3 :=
    sixPlus_complement_eq_oppositeFibreProjections label
  have hP0P3 : P0 * P3 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 0 3 (by decide)
  have hP0N1 : P0 * N1 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 0 1 (by decide)
  have hP0N2 : P0 * N2 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 0 2 (by decide)
  have hP3N1 : P3 * N1 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 3 1 (by decide)
  have hP3N2 : P3 * N2 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 3 2 (by decide)
  have hN2P3 : N2 * P3 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 2 3 (by decide)
  have hN1P3 : N1 * P3 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 1 3 (by decide)
  have hN1N2 : N1 * N2 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 1 2 (by decide)
  have hN2N1 : N2 * N1 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 2 1 (by decide)
  have hCN1 : C * N1 = 0 := by
    calc
      C * N1 = (P0 + P3) * N1 := by rw [hC]
      _ = P0 * N1 + P3 * N1 := by noncomm_ring
      _ = 0 := by rw [hP0N1, hP3N1]; simp
  have hCN2 : C * N2 = 0 := by
    calc
      C * N2 = (P0 + P3) * N2 := by rw [hC]
      _ = P0 * N2 + P3 * N2 := by noncomm_ring
      _ = 0 := by rw [hP0N2, hP3N2]; simp
  have hXN1 : X * N1 = 0 := by
    calc
      X * N1 = C * W * (C * N1) := by dsimp [X]; noncomm_ring
      _ = 0 := by rw [hCN1]; simp
  have hXN2 : X * N2 = 0 := by
    calc
      X * N2 = C * W * (C * N2) := by dsimp [X]; noncomm_ring
      _ = 0 := by rw [hCN2]; simp
  have hX02 := sixMatrix_neutralUndirectedEdge_X_product_zero
    P0 N2 X Y hXP0Y hXN2
  have hX31 := sixMatrix_neutralUndirectedEdge_X_product_zero
    P3 N1 X Y hXP3Y hXN1
  have hX01 := sixMatrix_neutralUndirectedEdge_X_product_zero
    P0 N1 X Y hXP0Y hXN1
  have hX32 := sixMatrix_neutralUndirectedEdge_X_product_zero
    P3 N2 X Y hXP3Y hXN2
  have h02_31 := sixMatrix_disjointNeutralEdges_product_zero
    P0 P3 N2 N1 Y hN2P3 hN2N1 hP0P3 hP0N1
  have h01_32 := sixMatrix_disjointNeutralEdges_product_zero
    P0 P3 N1 N2 Y hN1P3 hN1N2 hP0P3 hP0N2
  exact ⟨hX02, hX31, h02_31, hX01, hX32, h01_32⟩

end Neoplatonic.LTR
