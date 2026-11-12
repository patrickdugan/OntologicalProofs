import Neoplatonic.LTR.SixDimensionalNearHalfTransitionGramBudget
import Neoplatonic.LTR.SixDimensionalRealPauliDefectLeakage
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-168: quantitative singleton opposite-fibre row extinction

MAN-164 gives exact original six-dimensional complex transition-trace
identities with the nonsaturated defect Δ=I-(A+B)².

For a singleton corner fibre P0 or P3, the trace of the defect
compression costs at most ||Δ|| ≤ 2ε. Positive Pauli near-half overlap
forces E03 ≥ 1/4-ε/2.

The complete neutral-exchange transition energy leaving either
singleton corner therefore obeys

  Tr(P0 Y Yᴴ) ≤ 4ε   if m00=1,
  Tr(P3 Y Yᴴ) ≤ 4ε   if m11=1.

These inequalities hold in the original complex 6×6 coordinates
without saturation or a rank-one Gram hypothesis.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The scalar row-budget step: the surviving opposite energy
uses up the singleton output-fibre capacity to within 4ε. -/
theorem sixMatrix_nearHalf_singletonRow_scalarBudget
    (a b e z epsilon : ℝ)
    (hRow : a + b + z = 1 - 4 * e)
    (hEnergy : (1 / 4 : ℝ) - epsilon / 2 ≤ e)
    (hDefect : -2 * epsilon ≤ z) :
    a + b ≤ 4 * epsilon := by
  linarith

/-- Both singleton-corner row estimates follow from MAN-164,
in the genuine original Dirac coordinates. -/
theorem sixLabelled_exactHamming_positiveNearHalf_singletonCorner_rowBudget
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (epsilon : ℝ)
    (hc : 0 ≤ sixOrientedOppositeEnergyImbalance label D)
    (hnear : (1 / 2 : ℝ) - epsilon ≤
      sixOrientedOppositeEnergyImbalance label D) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let Y := (1 - Q : SixMat) * W * Q
    let P0 := sixTruthFibreProjection label 0
    let P3 := sixTruthFibreProjection label 3
    let N1 := sixTruthFibreProjection label 1
    let N2 := sixTruthFibreProjection label 2
    (truthMultiplicity label 0 = 1 →
      (sixMatrix_transitionTrace P0 Y N1).re +
        (sixMatrix_transitionTrace P0 Y N2).re ≤
          4 * epsilon) ∧
    (truthMultiplicity label 3 = 1 →
      (sixMatrix_transitionTrace P3 Y N1).re +
        (sixMatrix_transitionTrace P3 Y N2).re ≤
          4 * epsilon) := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let Y : SixMat := (1 - Q) * W * Q
  let Δ : SixMat := 1 - W * W
  let P0 : SixMat := sixTruthFibreProjection label 0
  let P3 : SixMat := sixTruthFibreProjection label 3
  let N1 : SixMat := sixTruthFibreProjection label 1
  let N2 : SixMat := sixTruthFibreProjection label 2
  let e : ℝ := sixTruthFibreBlockEnergy label D 0 3
  let z0 : ℂ := (P0 * Δ * P0).trace
  let z3 : ℂ := (P3 * Δ * P3).trace
  let a : ℝ := (sixMatrix_transitionTrace P0 Y N1).re
  let b : ℝ := (sixMatrix_transitionTrace P0 Y N2).re
  let c : ℝ := (sixMatrix_transitionTrace P3 Y N1).re
  let d : ℝ := (sixMatrix_transitionTrace P3 Y N2).re
  change (truthMultiplicity label 0 = 1 → a + b ≤ 4 * epsilon) ∧
    (truthMultiplicity label 3 = 1 → c + d ≤ 4 * epsilon)
  have hTable :=
    sixLabelled_plusWitness_nonsaturated_transitionTable_traceIdentities
      label D hD
  change
    ((sixMatrix_transitionTrace P0 Y N1 +
      sixMatrix_transitionTrace P0 Y N2 + z0 =
        (truthMultiplicity label 0 : ℂ) - 4 * (e : ℂ)) ∧
      (sixMatrix_transitionTrace P3 Y N1 +
        sixMatrix_transitionTrace P3 Y N2 + z3 =
          (truthMultiplicity label 3 : ℂ) - 4 * (e : ℂ))) ∧
    _ at hTable
  have hRow0 : a + b + z0.re =
      (truthMultiplicity label 0 : ℝ) - 4 * e := by
    have h := congrArg Complex.re hTable.1.1
    simpa [a, b, Complex.add_re, Complex.sub_re, Complex.mul_re] using h
  have hRow3 : c + d + z3.re =
      (truthMultiplicity label 3 : ℝ) - 4 * e := by
    have h := congrArg Complex.re hTable.1.2
    simpa [c, d, Complex.add_re, Complex.sub_re, Complex.mul_re] using h
  have hDef := sixLabelled_exactHamming_positiveNearHalf_defect_norm_le
    label D hD hham epsilon hc hnear
  change ‖Δ‖ ≤ 2 * epsilon at hDef
  have hE12 : (0 : ℝ) ≤ sixTruthFibreBlockEnergy label D 1 2 :=
    sixTruthFibreBlockEnergy_nonneg label D 1 2
  have hNearEnergy :
      (1 / 2 : ℝ) - epsilon ≤
        2 * (e - sixTruthFibreBlockEnergy label D 1 2) := hnear
  have hEnergy : (1 / 4 : ℝ) - epsilon / 2 ≤ e := by
    linarith
  constructor
  · intro hm0
    have hZ := sixTruthFibreProjection_defectTrace_norm_le
      label Δ 0
    change ‖z0‖ ≤ (truthMultiplicity label 0 : ℝ) * ‖Δ‖ at hZ
    rw [hm0] at hZ
    norm_num at hZ
    have hBound : ‖z0‖ ≤ 2 * epsilon :=
      hZ.trans hDef
    have hLower : -2 * epsilon ≤ z0.re := by
      have hRe := (abs_le.mp (Complex.abs_re_le_norm z0)).1
      linarith
    have hRow : a + b + z0.re = 1 - 4 * e := by
      simpa [hm0] using hRow0
    exact sixMatrix_nearHalf_singletonRow_scalarBudget
      a b e z0.re epsilon hRow hEnergy hLower
  · intro hm3
    have hZ := sixTruthFibreProjection_defectTrace_norm_le
      label Δ 3
    change ‖z3‖ ≤ (truthMultiplicity label 3 : ℝ) * ‖Δ‖ at hZ
    rw [hm3] at hZ
    norm_num at hZ
    have hBound : ‖z3‖ ≤ 2 * epsilon :=
      hZ.trans hDef
    have hLower : -2 * epsilon ≤ z3.re := by
      have hRe := (abs_le.mp (Complex.abs_re_le_norm z3)).1
      linarith
    have hRow : c + d + z3.re = 1 - 4 * e := by
      simpa [hm3] using hRow3
    exact sixMatrix_nearHalf_singletonRow_scalarBudget
      c d e z3.re epsilon hRow hEnergy hLower

end Neoplatonic.LTR
