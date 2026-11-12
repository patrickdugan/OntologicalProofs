import Neoplatonic.LTR.SixDimensionalApproximateNeutralEdgeOrthogonality
import Neoplatonic.LTR.SixDimensionalRealPauliDefectLeakage
import Neoplatonic.LTR.SixDimensionalActualNeutralEdgeOrthogonality
import Mathlib.Tactic

/-!
# LTR-MAN-150: actual near-saturated Dirac neutral edges are approximately orthogonal

MAN-147 supplies ||XY||<=2ε for the true six-dimensional positive
signed Hamming witness under c>=0 and c>=1/2-ε.

MAN-149 shows the two opposite truth-fibre projections P0,P3 split
the cross-channel product XY into small projected components. The
actual 00/11 corner X is off-diagonal and annihilates the 01/10
neutral fibres. All four fibre projections contract.

For each coordinate's pair of adjacent Hermitian neutral edges,
the true 6x6 Dirac chart consequently satisfies
  ||X E01||, ||X E32|| <=2ε,   E01 E32=0,
  ||X E02||, ||X E31|| <=2ε,   E02 E31=0.

These are direct quantitative replacements for MAN-125's zero
products, without assuming any saturated opposite-corner energy.
All four norms use the original Hermitian Dirac witness and its
unit-sized diagonal truth-fibre projectors.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Positive near-half Pauli overlap forces the actual opposite
signed corner to have at most 2ε interaction with each true
adjacent neutral edge, for both original coordinate operators.
Disjoint adjacent neutral edges have exact zero mutual product. -/
theorem sixLabelled_exactHamming_positiveNearHalf_actualEdges_smallProducts
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (ε : ℝ)
    (hc : 0 ≤ sixOrientedOppositeEnergyImbalance label D)
    (hnear : (1 / 2 : ℝ) - ε ≤
      sixOrientedOppositeEnergyImbalance label D) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    let X := C * W * C
    let Y := C * W * Q
    let P0 := sixTruthFibreProjection label 0
    let P3 := sixTruthFibreProjection label 3
    let N1 := sixTruthFibreProjection label 1
    let N2 := sixTruthFibreProjection label 2
    let E01 := sixMatrix_neutralUndirectedEdge P0 N1 Y
    let E32 := sixMatrix_neutralUndirectedEdge P3 N2 Y
    let E02 := sixMatrix_neutralUndirectedEdge P0 N2 Y
    let E31 := sixMatrix_neutralUndirectedEdge P3 N1 Y
    ‖X * E01‖ ≤ 2 * ε ∧
      ‖X * E32‖ ≤ 2 * ε ∧ E01 * E32 = 0 ∧
      ‖X * E02‖ ≤ 2 * ε ∧
      ‖X * E31‖ ≤ 2 * ε ∧ E02 * E31 = 0 := by
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
    ‖X * sixMatrix_neutralUndirectedEdge P0 N1 Y‖ ≤ 2 * ε ∧
    ‖X * sixMatrix_neutralUndirectedEdge P3 N2 Y‖ ≤ 2 * ε ∧
    sixMatrix_neutralUndirectedEdge P0 N1 Y *
      sixMatrix_neutralUndirectedEdge P3 N2 Y = 0 ∧
    ‖X * sixMatrix_neutralUndirectedEdge P0 N2 Y‖ ≤ 2 * ε ∧
    ‖X * sixMatrix_neutralUndirectedEdge P3 N1 Y‖ ≤ 2 * ε ∧
    sixMatrix_neutralUndirectedEdge P0 N2 Y *
      sixMatrix_neutralUndirectedEdge P3 N1 Y = 0
  have hP0id : P0 * P0 = P0 := by
    simpa only [P0, sixTruthFibreProjection, sixTruthSectorProjection]
      using (sixTruthSectorProjection_idempotent label (fun t : Fin 4 => t = 0))
  have hP3id : P3 * P3 = P3 := by
    simpa only [P3, sixTruthFibreProjection, sixTruthSectorProjection]
      using (sixTruthSectorProjection_idempotent label (fun t : Fin 4 => t = 3))
  have hP0P3 : P0 * P3 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 0 3 (by decide)
  have hP3P0 : P3 * P0 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 3 0 (by decide)
  have hP0N1 : P0 * N1 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 0 1 (by decide)
  have hP0N2 : P0 * N2 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 0 2 (by decide)
  have hP3N1 : P3 * N1 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 3 1 (by decide)
  have hP3N2 : P3 * N2 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 3 2 (by decide)
  have hN1P3 : N1 * P3 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 1 3 (by decide)
  have hN2P3 : N2 * P3 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 2 3 (by decide)
  have hN1N2 : N1 * N2 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 1 2 (by decide)
  have hN2N1 : N2 * N1 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 2 1 (by decide)
  have hC : C = P0 + P3 :=
    sixPlus_complement_eq_oppositeFibreProjections label
  have hC2 : C * C = C := by
    rw [hC]
    calc
      (P0 + P3) * (P0 + P3) =
          P0 * P0 + P0 * P3 + P3 * P0 + P3 * P3 := by noncomm_ring
      _ = P0 + P3 := by
        rw [hP0id, hP0P3, hP3P0, hP3id]
        simp
  have hYrange : (P0 + P3) * Y = Y := by
    calc
      (P0 + P3) * Y = C * (C * W * Q) := by rw [← hC]
      _ = (C * C) * W * Q := by noncomm_ring
      _ = Y := by rw [hC2]
  have hXoff : X = P0 * X * P3 + P3 * X * P0 :=
    sixLabelled_plusWitness_actualCorner_offdiagonal label D
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
  have hP0norm : ‖P0‖ ≤ (1 : ℝ) := by
    change ‖sixTruthSectorProjection label (fun t : Fin 4 => t = 0)‖ ≤ 1
    exact sixTruthSectorProjection_generic_norm_le_one
      label (fun t : Fin 4 => t = 0)
  have hP3norm : ‖P3‖ ≤ (1 : ℝ) := by
    change ‖sixTruthSectorProjection label (fun t : Fin 4 => t = 3)‖ ≤ 1
    exact sixTruthSectorProjection_generic_norm_le_one
      label (fun t : Fin 4 => t = 3)
  have hN1norm : ‖N1‖ ≤ (1 : ℝ) := by
    change ‖sixTruthSectorProjection label (fun t : Fin 4 => t = 1)‖ ≤ 1
    exact sixTruthSectorProjection_generic_norm_le_one
      label (fun t : Fin 4 => t = 1)
  have hN2norm : ‖N2‖ ≤ (1 : ℝ) := by
    change ‖sixTruthSectorProjection label (fun t : Fin 4 => t = 2)‖ ≤ 1
    exact sixTruthSectorProjection_generic_norm_le_one
      label (fun t : Fin 4 => t = 2)
  have hLeak := sixLabelled_exactHamming_positiveNearHalf_cornerLeakage
    label D hD hham ε hc hnear
  change ‖X * Y‖ ≤ 2 * ε ∧
    ‖Y.conjTranspose * Y - Q‖ ≤ 2 * ε at hLeak
  have hXY : ‖X * Y‖ ≤ 2 * ε := hLeak.1
  have hκ : (0 : ℝ) ≤ 2 * ε :=
    (norm_nonneg (X * Y)).trans hXY
  have h01_32 :=
    sixMatrix_offdiagonal_threeEdge_approxOrthogonal
      P0 P3 N1 N2 X Y (2 * ε)
      hP0id hP3id hP0P3 hP3P0 hXoff hYrange
      hP0norm hP3norm hN1norm hN2norm
      hXN1 hXN2 hN1P3 hN1N2 hP0N2 hκ hXY
  have h02_31 :=
    sixMatrix_offdiagonal_threeEdge_approxOrthogonal
      P0 P3 N2 N1 X Y (2 * ε)
      hP0id hP3id hP0P3 hP3P0 hXoff hYrange
      hP0norm hP3norm hN2norm hN1norm
      hXN2 hXN1 hN2P3 hN2N1 hP0N1 hκ hXY
  exact ⟨h01_32.1, h01_32.2.1, h01_32.2.2,
    h02_31.1, h02_31.2.1, h02_31.2.2⟩

end Neoplatonic.LTR
