import Neoplatonic.LTR.SixDimensionalNearHalfTransitionGramBudget
import Neoplatonic.LTR.SixDimensionalApproxBistochasticFourChannelGate
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-165: actual positive near-half Dirac transition table error budgets

MAN-164 certifies exact original 6D complex trace identities for the
four corner-to-neutral exchanges of the signed witness W=A+B.

For the opposite-double multiplicity (2,1,1,2) and near-positive
Pauli overlap c >= 1/2 - epsilon, the rows have total energies at most
1+6epsilon, and the columns have energies at least 1-2epsilon.

The 6epsilon follows from E03 >= 1/4-epsilon/2, plus at most
two diagonal defect entries on each rank-two opposite fibre.
The 2epsilon follows from the singleton neutral input and
||I-W²|| <= 2epsilon.

The transition values are the real parts of genuine 6x6 Gram traces.
They are nonnegative by MAN-118. No pure saturation is assumed.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Every true Hermitian truth-fibre Gram transition has a
nonnegative real trace, independently of fibre multiplicities. -/
theorem sixTruthFibre_transitionTrace_real_nonneg
    (label : Fin 6 → Fin 4) (Y : SixMat)
    (u v : Fin 4) :
    0 ≤ (sixMatrix_transitionTrace
      (sixTruthFibreProjection label u) Y
      (sixTruthFibreProjection label v)).re := by
  let P : SixMat := sixTruthFibreProjection label u
  let N : SixMat := sixTruthFibreProjection label v
  have hP2 : P * P = P := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection]
      using (sixTruthSectorProjection_idempotent label
        (fun t : Fin 4 => t = u))
  have hN2 : N * N = N := by
    simpa only [N, sixTruthFibreProjection, sixTruthSectorProjection]
      using (sixTruthSectorProjection_idempotent label
        (fun t : Fin 4 => t = v))
  have hPH : P.IsHermitian := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection]
      using (sixTruthSectorProjection_isHermitian label
        (fun t : Fin 4 => t = u))
  have hNH : N.IsHermitian := by
    simpa only [N, sixTruthFibreProjection, sixTruthSectorProjection]
      using (sixTruthSectorProjection_isHermitian label
        (fun t : Fin 4 => t = v))
  obtain ⟨e, he, htrace⟩ :=
    sixMatrix_transitionTrace_nonnegativeReal P N Y
      hP2 hN2 hPH hNH
  change sixMatrix_transitionTrace P Y N = (e : ℂ) at htrace
  change 0 ≤ (sixMatrix_transitionTrace P Y N).re
  rw [htrace]
  simpa using he

/-- The four true original-coordinate positive transition traces
obey the exact row/column error budgets needed by MAN-163 in the
opposite-double fibre multiplicity (2,1,1,2). -/
theorem sixLabelled_exactHamming_positiveNearHalf_oppositeDouble_transitionBudgets
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm0 : truthMultiplicity label 0 = 2)
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1)
    (hm3 : truthMultiplicity label 3 = 2)
    (epsilon : ℝ)
    (hc : 0 ≤ sixOrientedOppositeEnergyImbalance label D)
    (hnear : (1 / 2 : ℝ) - epsilon ≤
      sixOrientedOppositeEnergyImbalance label D) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    let Y := C * W * Q
    let P0 := sixTruthFibreProjection label 0
    let P3 := sixTruthFibreProjection label 3
    let N1 := sixTruthFibreProjection label 1
    let N2 := sixTruthFibreProjection label 2
    let a := (sixMatrix_transitionTrace P0 Y N1).re
    let b := (sixMatrix_transitionTrace P0 Y N2).re
    let c := (sixMatrix_transitionTrace P3 Y N1).re
    let d := (sixMatrix_transitionTrace P3 Y N2).re
    (0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d) ∧
    (a + b ≤ 1 + 6 * epsilon ∧
       c + d ≤ 1 + 6 * epsilon) ∧
    (1 - 2 * epsilon ≤ a + c ∧
       1 - 2 * epsilon ≤ b + d) := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let Y : SixMat := C * W * Q
  let Δ : SixMat := 1 - W * W
  let P0 : SixMat := sixTruthFibreProjection label 0
  let P3 : SixMat := sixTruthFibreProjection label 3
  let N1 : SixMat := sixTruthFibreProjection label 1
  let N2 : SixMat := sixTruthFibreProjection label 2
  let e : ℝ := sixTruthFibreBlockEnergy label D 0 3
  let z0 : ℂ := (P0 * Δ * P0).trace
  let z3 : ℂ := (P3 * Δ * P3).trace
  let z1 : ℂ := (N1 * Δ * N1).trace
  let z2 : ℂ := (N2 * Δ * N2).trace
  let ac : ℂ := sixMatrix_transitionTrace P0 Y N1
  let bc : ℂ := sixMatrix_transitionTrace P0 Y N2
  let cc : ℂ := sixMatrix_transitionTrace P3 Y N1
  let dc : ℂ := sixMatrix_transitionTrace P3 Y N2
  let a : ℝ := ac.re
  let b : ℝ := bc.re
  let c : ℝ := cc.re
  let d : ℝ := dc.re
  change (0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d) ∧
    (a + b ≤ 1 + 6 * epsilon ∧ c + d ≤ 1 + 6 * epsilon) ∧
    (1 - 2 * epsilon ≤ a + c ∧ 1 - 2 * epsilon ≤ b + d)
  have hTable := sixLabelled_plusWitness_nonsaturated_transitionTable_traceIdentities
    label D hD
  change (ac + bc + z0 =
      (truthMultiplicity label 0 : ℂ) - 4 * (e : ℂ) ∧
    cc + dc + z3 =
      (truthMultiplicity label 3 : ℂ) - 4 * (e : ℂ)) ∧
    (ac + cc + z1 = (truthMultiplicity label 1 : ℂ) ∧
     bc + dc + z2 = (truthMultiplicity label 2 : ℂ)) at hTable
  have hRow0 : a + b + z0.re = 2 - 4 * e := by
    have h := congrArg Complex.re hTable.1.1
    simpa [a, b, Complex.add_re, Complex.sub_re, Complex.mul_re, hm0] using h
  have hRow3 : c + d + z3.re = 2 - 4 * e := by
    have h := congrArg Complex.re hTable.1.2
    simpa [c, d, Complex.add_re, Complex.sub_re, Complex.mul_re, hm3] using h
  have hCol1 : a + c + z1.re = 1 := by
    have h := congrArg Complex.re hTable.2.1
    simpa [a, c, Complex.add_re, hm1] using h
  have hCol2 : b + d + z2.re = 1 := by
    have h := congrArg Complex.re hTable.2.2
    simpa [b, d, Complex.add_re, hm2] using h
  have hDef := sixLabelled_exactHamming_positiveNearHalf_defect_norm_le
    label D hD hham epsilon hc hnear
  change ‖Δ‖ ≤ 2 * epsilon at hDef
  have hE12 : 0 ≤ sixTruthFibreBlockEnergy label D 1 2 :=
    sixTruthFibreBlockEnergy_nonneg label D 1 2
  have hNearEnergy : (1 / 2 : ℝ) - epsilon ≤
      2 * (e - sixTruthFibreBlockEnergy label D 1 2) := hnear
  have hE03lower : (1 / 4 : ℝ) - epsilon / 2 ≤ e := by
    linarith
  have hZ0 := sixTruthFibreProjection_defectTrace_norm_le
    label Δ 0
  change ‖z0‖ ≤ (truthMultiplicity label 0 : ℝ) * ‖Δ‖ at hZ0
  rw [hm0] at hZ0
  have hz0 : ‖z0‖ ≤ 4 * epsilon := by
    nlinarith [norm_nonneg Δ]
  have hZ3 := sixTruthFibreProjection_defectTrace_norm_le
    label Δ 3
  change ‖z3‖ ≤ (truthMultiplicity label 3 : ℝ) * ‖Δ‖ at hZ3
  rw [hm3] at hZ3
  have hz3 : ‖z3‖ ≤ 4 * epsilon := by
    nlinarith [norm_nonneg Δ]
  have hZ1 := sixTruthFibreProjection_defectTrace_norm_le
    label Δ 1
  change ‖z1‖ ≤ (truthMultiplicity label 1 : ℝ) * ‖Δ‖ at hZ1
  rw [hm1] at hZ1
  have hz1 : ‖z1‖ ≤ 2 * epsilon := by
    nlinarith [norm_nonneg Δ]
  have hZ2 := sixTruthFibreProjection_defectTrace_norm_le
    label Δ 2
  change ‖z2‖ ≤ (truthMultiplicity label 2 : ℝ) * ‖Δ‖ at hZ2
  rw [hm2] at hZ2
  have hz2 : ‖z2‖ ≤ 2 * epsilon := by
    nlinarith [norm_nonneg Δ]
  have hz0lower : -4 * epsilon ≤ z0.re := by
    have h := (abs_le.mp (Complex.abs_re_le_norm z0)).1
    linarith
  have hz3lower : -4 * epsilon ≤ z3.re := by
    have h := (abs_le.mp (Complex.abs_re_le_norm z3)).1
    linarith
  have hz1upper : z1.re ≤ 2 * epsilon := by
    have h := (abs_le.mp (Complex.abs_re_le_norm z1)).2
    linarith
  have hz2upper : z2.re ≤ 2 * epsilon := by
    have h := (abs_le.mp (Complex.abs_re_le_norm z2)).2
    linarith
  have ha : 0 ≤ a :=
    sixTruthFibre_transitionTrace_real_nonneg label Y 0 1
  have hb : 0 ≤ b :=
    sixTruthFibre_transitionTrace_real_nonneg label Y 0 2
  have hc' : 0 ≤ c :=
    sixTruthFibre_transitionTrace_real_nonneg label Y 3 1
  have hd : 0 ≤ d :=
    sixTruthFibre_transitionTrace_real_nonneg label Y 3 2
  exact ⟨⟨ha, hb, hc', hd⟩,
    ⟨by linarith, by linarith⟩,
    ⟨by linarith, by linarith⟩⟩

end Neoplatonic.LTR
