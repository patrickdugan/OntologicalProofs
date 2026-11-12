import Neoplatonic.LTR.SixDimensionalPositiveDefectDiagonal
import Neoplatonic.LTR.SixDimensionalNearHalfActualBistochasticBudgets
import Neoplatonic.LTR.SixDimensionalNearHalfNeutralSingletons
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-173: sharper near-half energy and transition row bounds

MAN-172 supplies nonnegative real spectral-defect diagonals for the
actual positive signed Hamming witness W=A+B. Its one-sided signed
trace correction improves the MAN-161/162 opposite energy estimate
whenever both neutral truth fibres are singleton:

  E03 <= 1/4+epsilon/2,
  E12 <= epsilon,
  ||J||² <= epsilon.

Moreover the two output-fibre correction traces in MAN-164 are
nonnegative. For the opposite-double (2,1,1,2) pattern, the 2×2
transition table's row sums are at most 1+2epsilon. The column lower
bounds 1-2epsilon of MAN-165 remain valid.

These estimates are exact operator/matrix necessities for the
original six-dimensional labelled Hermitian Dirac representation,
independent of spectral saturation.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The one-sided signed trace inequality improves the oriented
00/11 energy upper bound to quarter plus half the positive
Pauli slack as soon as the neutral input fibres are singleton. -/
theorem sixLabelled_exactHamming_positiveNearHalf_E03_upper_sharp
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (epsilon : ℝ)
    (hc : 0 ≤ sixOrientedOppositeEnergyImbalance label D)
    (hnear : (1 / 2 : ℝ) - epsilon ≤
      sixOrientedOppositeEnergyImbalance label D)
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1) :
    sixTruthFibreBlockEnergy label D 0 3 ≤
      (1 / 4 : ℝ) + epsilon / 2 := by
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Δ : SixMat := 1 - W * W
  let S : ℂ := ∑ i : Fin 6,
    if squarePlusNeutral (label i) then -(Δ i i) else Δ i i
  let e : ℝ := sixTruthFibreBlockEnergy label D 0 3
  have hW : ‖W‖ ≤ (1 : ℝ) :=
    sixLabelled_exactHamming_plusWitness_norm_le_one label D hD hham
  have hDdiag : ∀ i : Fin 6, 0 ≤ (Δ i i).re :=
    fun i => sixMatrix_contraction_squareDefect_diagonal_re_nonneg W hW i
  have hSigned := sixMatrix_signedDiagonal_re_lower_of_nonneg
    Δ (fun i => squarePlusNeutral (label i)) hDdiag
  change -((Finset.univ.filter
    (fun i : Fin 6 => squarePlusNeutral (label i))).card : ℝ) *
      ‖Δ‖ ≤ S.re at hSigned
  rw [sixPlusNeutral_card_eq_fibreSum label, hm1, hm2] at hSigned
  norm_num at hSigned
  have hDef := sixLabelled_exactHamming_positiveNearHalf_defect_norm_le
    label D hD hham epsilon hc hnear
  change ‖Δ‖ ≤ 2 * epsilon at hDef
  have hLower : -(4 * epsilon) ≤ S.re := by linarith
  have hId := sixLabelled_plusWitness_traceDefect_signedIdentity
    label D hD
  change (6 : ℂ) =
    2 * ((truthMultiplicity label 1 +
      truthMultiplicity label 2 : ℕ) : ℂ) +
    8 * (e : ℂ) + S at hId
  rw [hm1, hm2] at hId
  have hReal : (8 : ℝ) * e + S.re = 2 := by
    have h := congrArg Complex.re hId
    norm_num [Complex.add_re, Complex.mul_re] at h
    linarith
  change e ≤ (1 / 4 : ℝ) + epsilon / 2
  linarith

/-- Positive near-half spectral overlap forces the opposite
01/10 original Dirac energy to be at most epsilon, sharpening
MAN-162's earlier 2epsilon bound for all faithful patterns. -/
theorem sixLabelled_exactHamming_positiveNearHalf_E12_le_epsilon
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (epsilon : ℝ)
    (hnear : (1 / 2 : ℝ) - epsilon ≤
      sixOrientedOppositeEnergyImbalance label D)
    (hsmall : epsilon < (1 / 8 : ℝ)) :
    sixTruthFibreBlockEnergy label D 1 2 ≤ epsilon := by
  obtain ⟨hm1, hm2⟩ :=
    sixLabelled_exactHamming_positiveNearHalf_neutralSingletons
      label D hsurj hD hham epsilon hnear hsmall
  have hc : 0 ≤ sixOrientedOppositeEnergyImbalance label D := by
    linarith
  have hUp := sixLabelled_exactHamming_positiveNearHalf_E03_upper_sharp
    label D hD hham epsilon hc hnear hm1 hm2
  have hNear : (1 / 2 : ℝ) - epsilon ≤
    2 * (sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2) := hnear
  linarith

/-- All faithful six-dimensional positive near-half charts have
a genuinely original fourth-edge squared norm at most epsilon. -/
theorem sixLabelled_exactHamming_positiveNearHalf_J_normSq_le_epsilon
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (epsilon : ℝ)
    (hnear : (1 / 2 : ℝ) - epsilon ≤
      sixOrientedOppositeEnergyImbalance label D)
    (hsmall : epsilon < (1 / 8 : ℝ)) :
    ‖sixPlusOppositeNeutralEdge label D‖ *
      ‖sixPlusOppositeNeutralEdge label D‖ ≤ epsilon := by
  obtain ⟨hm1, _⟩ :=
    sixLabelled_exactHamming_positiveNearHalf_neutralSingletons
      label D hsurj hD hham epsilon hnear hsmall
  rw [sixLabelled_singletonNeutral1_fourthEdge_normSq_eq_energy12
    label D hD hm1]
  exact sixLabelled_exactHamming_positiveNearHalf_E12_le_epsilon
    label D hsurj hD hham epsilon hnear hsmall

/-- The genuine 2×2 output transition rows are bounded by
1+2epsilon once the spectral-defect fibre traces are known
nonnegative, improving MAN-165's previous 1+6epsilon. -/
theorem sixLabelled_exactHamming_positiveNearHalf_oppositeDouble_rows_sharp
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm0 : truthMultiplicity label 0 = 2)
    (hm3 : truthMultiplicity label 3 = 2)
    (epsilon : ℝ)
    (hnear : (1 / 2 : ℝ) - epsilon ≤
      sixOrientedOppositeEnergyImbalance label D) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let Y := (1 - Q : SixMat) * W * Q
    let P0 := sixTruthFibreProjection label 0
    let P3 := sixTruthFibreProjection label 3
    let N1 := sixTruthFibreProjection label 1
    let N2 := sixTruthFibreProjection label 2
    (sixMatrix_transitionTrace P0 Y N1).re +
      (sixMatrix_transitionTrace P0 Y N2).re ≤
        1 + 2 * epsilon ∧
    (sixMatrix_transitionTrace P3 Y N1).re +
      (sixMatrix_transitionTrace P3 Y N2).re ≤
        1 + 2 * epsilon := by
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
  let a : ℂ := sixMatrix_transitionTrace P0 Y N1
  let b : ℂ := sixMatrix_transitionTrace P0 Y N2
  let c : ℂ := sixMatrix_transitionTrace P3 Y N1
  let d : ℂ := sixMatrix_transitionTrace P3 Y N2
  change a.re + b.re ≤ 1 + 2 * epsilon ∧
    c.re + d.re ≤ 1 + 2 * epsilon
  have hTrace :=
    sixLabelled_plusWitness_nonsaturated_transitionTable_traceIdentities
      label D hD
  change (a + b + z0 =
      (truthMultiplicity label 0 : ℂ) - 4 * (e : ℂ) ∧
    c + d + z3 =
      (truthMultiplicity label 3 : ℂ) - 4 * (e : ℂ)) ∧ _ at hTrace
  have hRow0 : a.re + b.re + z0.re = 2 - 4 * e := by
    have h := congrArg Complex.re hTrace.1.1
    simpa [Complex.add_re, Complex.sub_re, Complex.mul_re, hm0] using h
  have hRow3 : c.re + d.re + z3.re = 2 - 4 * e := by
    have h := congrArg Complex.re hTrace.1.2
    simpa [Complex.add_re, Complex.sub_re, Complex.mul_re, hm3] using h
  have hZ0 : 0 ≤ z0.re :=
    sixLabelled_exactHamming_plusDefect_fibreTrace_re_nonneg
      label D hD hham 0
  have hZ3 : 0 ≤ z3.re :=
    sixLabelled_exactHamming_plusDefect_fibreTrace_re_nonneg
      label D hD hham 3
  have hE12 : (0 : ℝ) ≤ sixTruthFibreBlockEnergy label D 1 2 :=
    sixTruthFibreBlockEnergy_nonneg label D 1 2
  have hNear : (1 / 2 : ℝ) - epsilon ≤
    2 * (e - sixTruthFibreBlockEnergy label D 1 2) := hnear
  have hELower : (1 / 4 : ℝ) - epsilon / 2 ≤ e := by
    linarith
  constructor <;> linarith

/-- The genuine 2×2 transition energy table has nonnegative
entries, row error rho=2epsilon and column error sigma=2epsilon. -/
theorem sixLabelled_exactHamming_positiveNearHalf_oppositeDouble_transitionBudgets_sharp
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
    let Y := (1 - Q : SixMat) * W * Q
    let P0 := sixTruthFibreProjection label 0
    let P3 := sixTruthFibreProjection label 3
    let N1 := sixTruthFibreProjection label 1
    let N2 := sixTruthFibreProjection label 2
    let a := (sixMatrix_transitionTrace P0 Y N1).re
    let b := (sixMatrix_transitionTrace P0 Y N2).re
    let c := (sixMatrix_transitionTrace P3 Y N1).re
    let d := (sixMatrix_transitionTrace P3 Y N2).re
    (0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ 0 ≤ d) ∧
    (a + b ≤ 1 + 2 * epsilon ∧
      c + d ≤ 1 + 2 * epsilon) ∧
    (1 - 2 * epsilon ≤ a + c ∧
      1 - 2 * epsilon ≤ b + d) := by
  dsimp only
  have hOld :=
    sixLabelled_exactHamming_positiveNearHalf_oppositeDouble_transitionBudgets
      label D hD hham hm0 hm1 hm2 hm3 epsilon hc hnear
  dsimp only at hOld
  have hRows :=
    sixLabelled_exactHamming_positiveNearHalf_oppositeDouble_rows_sharp
      label D hD hham hm0 hm3 epsilon hnear
  dsimp only at hRows
  exact ⟨hOld.1, hRows, hOld.2.2⟩

end Neoplatonic.LTR
