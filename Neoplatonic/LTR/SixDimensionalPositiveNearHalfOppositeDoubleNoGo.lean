import Neoplatonic.LTR.SixDimensionalRationalNearHalfFourChannelGate
import Neoplatonic.LTR.SixDimensionalNearHalfActualBistochasticBudgets
import Neoplatonic.LTR.SixDimensionalActualNearHalfNeutralEdgeLeakage
import Neoplatonic.LTR.SixDimensionalSaturated03ActualNormNoGo
import Neoplatonic.LTR.SixDimensionalUniformHalfCornerBound
import Neoplatonic.LTR.SixDimensionalNonsaturatedCoordinateFourEdges
import Neoplatonic.LTR.SixDimensionalNearHalfNeutralSingletons
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-167: the true positive near-half opposite-double obstruction

Combine the merged original-coordinate estimates MAN-150, MAN-154,
MAN-157, MAN-162 and MAN-165 with MAN-166's rational C*-norm gate.

In the faithful (2,1,1,2) truth-fibre chart, exact Hamming and
c >= 1/2-1/250 imply an impossibility for a single common
Hermitian complex six-dimensional Dirac matrix.

The 01/10 neutral fibres are singleton, so each Hermitian adjacent
edge's squared operator norm equals the corresponding nonnegative
transition Gram-trace energy. The shared opposite corner H=X/2
has norm <=1/2, cross products <=1/250, and the genuinely
nonsaturated fourth edge obeys ||J||²<=2/250.

No saturation equations, arbitrary U(2) gauge, or new axioms.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A singleton neutral input makes the true undirected edge
operator norm square exactly the real part of its transition
Gram trace, with no basis choice and no saturation hypothesis. -/
theorem sixMatrix_singletonNeutralEdge_normSq_eq_transitionTraceRe
    (label : Fin 6 → Fin 4) (u : Fin 4)
    (hMult : truthMultiplicity label u = 1)
    (P Y : SixMat)
    (hPid : P * P = P) (hPH : P.IsHermitian)
    (hPN : P * sixTruthFibreProjection label u = 0)
    (hNP : sixTruthFibreProjection label u * P = 0) :
    ‖sixMatrix_neutralUndirectedEdge
        P (sixTruthFibreProjection label u) Y‖ *
      ‖sixMatrix_neutralUndirectedEdge
        P (sixTruthFibreProjection label u) Y‖ =
      (sixMatrix_transitionTrace P Y
        (sixTruthFibreProjection label u)).re := by
  obtain ⟨e, _, hTrace, hNorm⟩ :=
    sixMatrix_singletonNeutralEdge_trace_eq_normSq
      label u hMult P Y hPid hPH hPN hNP
  change sixMatrix_transitionTrace P Y
    (sixTruthFibreProjection label u) = (e : ℂ) at hTrace
  calc
    ‖sixMatrix_neutralUndirectedEdge
        P (sixTruthFibreProjection label u) Y‖ *
      ‖sixMatrix_neutralUndirectedEdge
        P (sixTruthFibreProjection label u) Y‖ = e := hNorm
    _ = (sixMatrix_transitionTrace P Y
          (sixTruthFibreProjection label u)).re := by
            rw [hTrace]
            simp

/-- MAN-150's 2ε bound on an original corner-neutral product
becomes ε for the genuine common half-corner H=X/2. -/
theorem sixMatrix_halfCorner_edgeProduct_oneOver250
    (H X E : SixMat)
    (hH : H = (1 / 2 : ℂ) • X)
    (hXE : ‖X * E‖ ≤ (2 / 250 : ℝ)) :
    ‖H * E‖ ≤ (1 / 250 : ℝ) := by
  calc
    ‖H * E‖ = ‖(1 / 2 : ℂ) • (X * E)‖ := by
      rw [hH, Matrix.smul_mul]
    _ = (1 / 2 : ℝ) * ‖X * E‖ := by
      rw [norm_smul]
      norm_num
    _ ≤ (1 / 2 : ℝ) * (2 / 250 : ℝ) :=
      mul_le_mul_of_nonneg_left hXE (by norm_num)
    _ = (1 / 250 : ℝ) := by norm_num

/-- A faithful opposite-double labelled complex six-dimensional
Dirac representation cannot realize exact Connes Hamming distances
when its positive residual Pauli overlap is within 1/250 of 1/2. -/
theorem sixLabelled_exactHamming_positiveNearHalf_oppositeDouble_impossible
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm0 : truthMultiplicity label 0 = 2)
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1)
    (hm3 : truthMultiplicity label 3 = 2)
    (hnear : (1 / 2 : ℝ) - (1 / 250 : ℝ) ≤
      sixOrientedOppositeEnergyImbalance label D) :
    False := by
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let X : SixMat := C * W * C
  let Y : SixMat := C * W * Q
  let P0 : SixMat := sixTruthFibreProjection label 0
  let P3 : SixMat := sixTruthFibreProjection label 3
  let N1 : SixMat := sixTruthFibreProjection label 1
  let N2 : SixMat := sixTruthFibreProjection label 2
  let H : SixMat := sixPlusActiveHalf label D
  let J : SixMat := sixPlusOppositeNeutralEdge label D
  let E01 : SixMat := sixMatrix_neutralUndirectedEdge P0 N1 Y
  let E32 : SixMat := sixMatrix_neutralUndirectedEdge P3 N2 Y
  let E02 : SixMat := sixMatrix_neutralUndirectedEdge P0 N2 Y
  let E31 : SixMat := sixMatrix_neutralUndirectedEdge P3 N1 Y
  let a : ℝ := (sixMatrix_transitionTrace P0 Y N1).re
  let b : ℝ := (sixMatrix_transitionTrace P0 Y N2).re
  let c : ℝ := (sixMatrix_transitionTrace P3 Y N1).re
  let d : ℝ := (sixMatrix_transitionTrace P3 Y N2).re
  have hc : 0 ≤ sixOrientedOppositeEnergyImbalance label D := by
    linarith [hnear]
  have hP02 : P0 * P0 = P0 := by
    simpa only [P0, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label (fun u : Fin 4 => u = 0))
  have hP32 : P3 * P3 = P3 := by
    simpa only [P3, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label (fun u : Fin 4 => u = 3))
  have hP0H : P0.IsHermitian := by
    simpa only [P0, sixTruthFibreProjection, sixTruthSectorProjection] using
      sixTruthSectorProjection_isHermitian label (fun u : Fin 4 => u = 0)
  have hP3H : P3.IsHermitian := by
    simpa only [P3, sixTruthFibreProjection, sixTruthSectorProjection] using
      sixTruthSectorProjection_isHermitian label (fun u : Fin 4 => u = 3)
  have hN1H : N1.IsHermitian := by
    simpa only [N1, sixTruthFibreProjection, sixTruthSectorProjection] using
      sixTruthSectorProjection_isHermitian label (fun u : Fin 4 => u = 1)
  have hN2H : N2.IsHermitian := by
    simpa only [N2, sixTruthFibreProjection, sixTruthSectorProjection] using
      sixTruthSectorProjection_isHermitian label (fun u : Fin 4 => u = 2)
  have hP0N1 : P0 * N1 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 0 1 (by decide)
  have hN1P0 : N1 * P0 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 1 0 (by decide)
  have hP0N2 : P0 * N2 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 0 2 (by decide)
  have hN2P0 : N2 * P0 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 2 0 (by decide)
  have hP3N1 : P3 * N1 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 3 1 (by decide)
  have hN1P3 : N1 * P3 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 1 3 (by decide)
  have hP3N2 : P3 * N2 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 3 2 (by decide)
  have hN2P3 : N2 * P3 = 0 :=
    sixTruthFibreProjection_mul_zero_of_distinct label 2 3 (by decide)
  have hWH : W.IsHermitian :=
    sixLabelled_plusWitness_isHermitian label D hD
  have hHH : H.IsHermitian := by
    have hh : (sixTruthUndirectedBlock label W 0 3).IsHermitian :=
      sixTruthUndirectedBlock_hermitian label W hWH 0 3
    change ((1 / 2 : ℂ) • sixTruthUndirectedBlock label W 0 3).conjTranspose =
      (1 / 2 : ℂ) • sixTruthUndirectedBlock label W 0 3
    rw [Matrix.conjTranspose_smul, hh.eq]
    norm_num
  have hE01H : E01.IsHermitian :=
    sixMatrix_neutralUndirectedEdge_hermitian P0 N1 Y hP0H hN1H
  have hE32H : E32.IsHermitian :=
    sixMatrix_neutralUndirectedEdge_hermitian P3 N2 Y hP3H hN2H
  have hE02H : E02.IsHermitian :=
    sixMatrix_neutralUndirectedEdge_hermitian P0 N2 Y hP0H hN2H
  have hE31H : E31.IsHermitian :=
    sixMatrix_neutralUndirectedEdge_hermitian P3 N1 Y hP3H hN1H
  have hHalf : H = (1 / 2 : ℂ) • X :=
    sixLabelled_plusActiveHalf_eq_trueCornerHalf label D
  have hHbound : ‖H‖ ≤ (1 / 2 : ℝ) :=
    sixLabelled_exactHamming_plusActiveHalf_norm_le label D hD hham
  have hProd := sixLabelled_exactHamming_positiveNearHalf_actualEdges_smallProducts
    label D hD hham (1 / 250 : ℝ) hc hnear
  change ‖X * E01‖ ≤ 2 * (1 / 250 : ℝ) ∧
    ‖X * E32‖ ≤ 2 * (1 / 250 : ℝ) ∧ E01 * E32 = 0 ∧
    ‖X * E02‖ ≤ 2 * (1 / 250 : ℝ) ∧
    ‖X * E31‖ ≤ 2 * (1 / 250 : ℝ) ∧ E02 * E31 = 0 at hProd
  obtain ⟨hXE01, hXE32, hE0132, hXE02, hXE31, hE0231⟩ := hProd
  have hHE01 : ‖H * E01‖ ≤ (1 / 250 : ℝ) :=
    sixMatrix_halfCorner_edgeProduct_oneOver250
      H X E01 hHalf (by nlinarith [hXE01])
  have hHE32 : ‖H * E32‖ ≤ (1 / 250 : ℝ) :=
    sixMatrix_halfCorner_edgeProduct_oneOver250
      H X E32 hHalf (by nlinarith [hXE32])
  have hHE02 : ‖H * E02‖ ≤ (1 / 250 : ℝ) :=
    sixMatrix_halfCorner_edgeProduct_oneOver250
      H X E02 hHalf (by nlinarith [hXE02])
  have hHE31 : ‖H * E31‖ ≤ (1 / 250 : ℝ) :=
    sixMatrix_halfCorner_edgeProduct_oneOver250
      H X E31 hHalf (by nlinarith [hXE31])
  have hJSq : ‖J‖ * ‖J‖ ≤ (2 / 250 : ℝ) := by
    have h := sixLabelled_exactHamming_positiveNearHalf_J_normSq_le_twoEpsilon
      label D hsurj hD hham (1 / 250 : ℝ) hnear
      (by norm_num)
    change ‖J‖ * ‖J‖ ≤ 2 * (1 / 250 : ℝ) at h
    nlinarith
  have hE01sq : ‖E01‖ * ‖E01‖ = a :=
    sixMatrix_singletonNeutralEdge_normSq_eq_transitionTraceRe
      label 1 hm1 P0 Y hP02 hP0H hP0N1 hN1P0
  have hE32sq : ‖E32‖ * ‖E32‖ = d :=
    sixMatrix_singletonNeutralEdge_normSq_eq_transitionTraceRe
      label 2 hm2 P3 Y hP32 hP3H hP3N2 hN2P3
  have hE02sq : ‖E02‖ * ‖E02‖ = b :=
    sixMatrix_singletonNeutralEdge_normSq_eq_transitionTraceRe
      label 2 hm2 P0 Y hP02 hP0H hP0N2 hN2P0
  have hE31sq : ‖E31‖ * ‖E31‖ = c :=
    sixMatrix_singletonNeutralEdge_normSq_eq_transitionTraceRe
      label 1 hm1 P3 Y hP32 hP3H hP3N1 hN1P3
  have hTable :=
    sixLabelled_exactHamming_positiveNearHalf_oppositeDouble_transitionBudgets
      label D hD hham hm0 hm1 hm2 hm3 (1 / 250 : ℝ) hc hnear
  change
    (0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d) ∧
    (a + b ≤ 1 + 6 * (1 / 250 : ℝ) ∧
      c + d ≤ 1 + 6 * (1 / 250 : ℝ)) ∧
    (1 - 2 * (1 / 250 : ℝ) ≤ a + c ∧
      1 - 2 * (1 / 250 : ℝ) ≤ b + d) at hTable
  obtain ⟨⟨ha, hb, hc', hd⟩, ⟨hRow0, hRow1⟩,
    ⟨hCol0, hCol1⟩⟩ := hTable
  have hE01block : E01 = sixTruthUndirectedBlock label W 0 1 :=
    sixLabelled_plusWitness_actualNeutralEdge_eq_truthBlock
      label D hD 0 1 (Or.inl rfl) (Or.inl rfl)
  have hE32block : E32 = sixTruthUndirectedBlock label W 3 2 :=
    sixLabelled_plusWitness_actualNeutralEdge_eq_truthBlock
      label D hD 3 2 (Or.inr rfl) (Or.inr rfl)
  have hE02block : E02 = sixTruthUndirectedBlock label W 0 2 :=
    sixLabelled_plusWitness_actualNeutralEdge_eq_truthBlock
      label D hD 0 2 (Or.inl rfl) (Or.inr rfl)
  have hE31block : E31 = sixTruthUndirectedBlock label W 3 1 :=
    sixLabelled_plusWitness_actualNeutralEdge_eq_truthBlock
      label D hD 3 1 (Or.inr rfl) (Or.inl rfl)
  have hA : labelledSquareA label D = H + E01 + E32 + J := by
    calc
      labelledSquareA label D = sixPlusCoordinateAAllFourEdges label D :=
        sixLabelled_coordinateA_fourEdges label D
      _ = H + E01 + E32 + J := by
        change (H + sixTruthUndirectedBlock label W 0 1 +
          sixTruthUndirectedBlock label W 2 3) + J =
          H + E01 + E32 + J
        rw [← hE01block, sixTruthUndirectedBlock_swap label W 2 3,
          ← hE32block]
  have hB : labelledSquareB label D = H + E02 + E31 - J := by
    calc
      labelledSquareB label D = sixPlusCoordinateBAllFourEdges label D :=
        sixLabelled_coordinateB_fourEdges label D
      _ = H + E02 + E31 - J := by
        change (H + sixTruthUndirectedBlock label W 0 2 +
          sixTruthUndirectedBlock label W 1 3) - J =
          H + E02 + E31 - J
        rw [← hE02block, sixTruthUndirectedBlock_swap label W 1 3,
          ← hE31block]
  have hd01 : sixLabelledConnesDistance label D 0 1 = 1 := by
    simpa [twoBitSquareHamming] using hham 0 1
  have hd02 : sixLabelledConnesDistance label D 0 2 = 1 := by
    simpa [twoBitSquareHamming] using hham 0 2
  have hAunit : (1 : ℝ) ≤ ‖labelledSquareA label D‖ := by
    have hedges : ∀ f : Fin 4 → ℂ,
        ‖sixLabelledDiracComm label D f‖ ≤ 1 →
        ‖f 0 - f 1‖ ≤ 1 := by
      intro f hf
      exact sixLabelledConnesDistance_bounds label D 0 1 1
        (by simp [hd01]) f hf
    have h := sixLabelled_firstCoordinate_norm_ge_one label D hedges
    change (1 : ℝ) ≤ ‖labelledSquareA label D‖ at h
    exact h
  have hBunit : (1 : ℝ) ≤ ‖labelledSquareB label D‖ := by
    have hedges : ∀ f : Fin 4 → ℂ,
        ‖sixLabelledDiracComm label D f‖ ≤ 1 →
        ‖f 0 - f 2‖ ≤ 1 := by
      intro f hf
      exact sixLabelledConnesDistance_bounds label D 0 2 1
        (by simp [hd02]) f hf
    have h := sixLabelled_secondCoordinate_norm_ge_one label D hedges
    change (1 : ℝ) ≤ ‖labelledSquareB label D‖ at h
    exact h
  exact sixMatrix_approxBistochastic_fourChannel_oneOver250_impossible
    H E01 E32 E02 E31 J
      (labelledSquareA label D) (labelledSquareB label D)
    hHH hE01H hE32H hE02H hE31H
    hE0132 hE0231 hHbound
    hHE01 hHE32 hHE02 hHE31 hJSq
    a b c d ha hb hc' hd
    hE01sq hE32sq hE02sq hE31sq
    (by nlinarith [hRow0]) (by nlinarith [hRow1])
    (by nlinarith [hCol0]) (by nlinarith [hCol1])
    hA hB hAunit hBunit

end Neoplatonic.LTR
