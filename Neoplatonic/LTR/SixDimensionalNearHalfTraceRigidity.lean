import Neoplatonic.LTR.SixDimensionalSignedWitnessTraceEnergy
import Neoplatonic.LTR.SixDimensionalRealPauliDefectLeakage
import Neoplatonic.LTR.SixDimensionalOppositeCornerEntryBound
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-161: quantitative six-dimensional signed trace rigidity

The exact involution trace identity MAN-92 extends to a nonsaturated
positive signed witness W with spectral defect Δ=I-W².

Let N be the {01,10} neutral truth sector of cardinality m.
The original witness's neutral-neutral block is zero; its 00/11
complementary square contribution is exactly 8 E03.

Therefore, for arbitrary Hermitian D and arbitrary truth labels,

  6 = 2m + 8 E03 +
        Σᵢ (if i ∈ N then -Δᵢᵢ else Δᵢᵢ).

The signed diagonal defect is at most six times the genuine
Euclidean Hilbert operator norm of Δ. MAN-147 provides
||Δ|| <= 2ε under positive near-half Pauli overlap, giving

  |8 E03 - (6 - 2m)| <= 12ε.

The whole proof uses the original complex 6×6 matrices and
truth-fibre multiplicities. No spectral saturation is assumed.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A signed sum of six diagonal entries is bounded by six times
the Euclidean Hilbert operator norm of the matrix. -/
theorem sixMatrix_signedDiagonalSum_norm_le_six
    (M : SixMat) (neutral : Fin 6 → Prop) [DecidablePred neutral] :
    ‖∑ i : Fin 6, if neutral i then -(M i i) else M i i‖ ≤
      6 * ‖M‖ := by
  have hentry (i : Fin 6) : ‖M i i‖ ≤ ‖M‖ := by
    rw [Matrix.cstar_norm_def]
    change ‖M i i‖ ≤ ‖M.toEuclideanLin.toContinuousLinearMap‖
    exact sixMatrix_entryNorm_le_operatorNorm M i i
  calc
    ‖∑ i : Fin 6, if neutral i then -(M i i) else M i i‖ ≤
        ∑ i : Fin 6, ‖if neutral i then -(M i i) else M i i‖ :=
          norm_sum_le _ _
    _ = ∑ i : Fin 6, ‖M i i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hn : neutral i <;> simp [hn]
    _ ≤ ∑ _i : Fin 6, ‖M‖ :=
      Finset.sum_le_sum (fun i _ => hentry i)
    _ = 6 * ‖M‖ := by simp [Fin.sum_univ_six]

/-- Generalization of MAN-92's exact trace-energy identity to
arbitrary, possibly nonsaturated, original Dirac matrices. -/
theorem sixLabelled_plusWitness_traceDefect_signedIdentity
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Δ : SixMat := 1 - W * W
    (6 : ℂ) =
      (2 : ℂ) * ((truthMultiplicity label 1 +
        truthMultiplicity label 2 : ℕ) : ℂ) +
      (8 : ℂ) * ((sixTruthFibreBlockEnergy label D 0 3 : ℝ) : ℂ) +
      (∑ i : Fin 6, if squarePlusNeutral (label i)
        then -(Δ i i) else Δ i i) := by
  dsimp only
  classical
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Δ : SixMat := 1 - W * W
  let neutral : Fin 6 → Prop := fun i => squarePlusNeutral (label i)
  let S : ℂ := ∑ i : Fin 6, Δ i i
  let SN : ℂ := ∑ i : Fin 6, if neutral i then Δ i i else 0
  let m : ℕ := truthMultiplicity label 1 + truthMultiplicity label 2
  let e : ℝ := sixTruthFibreBlockEnergy label D 0 3
  change (6 : ℂ) = 2 * (m : ℂ) + 8 * (e : ℂ) +
    (∑ i : Fin 6, if neutral i then -(Δ i i) else Δ i i)
  have hNN : ∀ i j : Fin 6, neutral i → neutral j →
      W i j * W j i = 0 := by
    intro i j hi hj
    exact sixLabelled_plusWitness_neutral_pair_zero label D i j hi hj
  have hTrace := sixMatrix_trace_square_neutral_decomposition
    W neutral hNN
  have hTraceDefect : (W * W).trace = (6 : ℂ) - S := by
    calc
      (W * W).trace = ∑ i : Fin 6, (W * W) i i := rfl
      _ = ∑ i : Fin 6, ((1 : ℂ) - Δ i i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [Δ, Matrix.sub_apply, Matrix.one_apply]
      _ = (6 : ℂ) - S := by
        simp [S, Finset.sum_sub_distrib, Fin.sum_univ_six]
  have hNeutralDefect :
      (∑ i : Fin 6, if neutral i then (W * W) i i else 0) =
        (m : ℂ) - SN := by
    have hpoint (i : Fin 6) :
        (if neutral i then (W * W) i i else 0) =
        (if neutral i then (1 : ℂ) else 0) -
          (if neutral i then Δ i i else 0) := by
      by_cases hi : neutral i <;>
        simp [hi, Δ, Matrix.sub_apply, Matrix.one_apply] <;> ring
    calc
      _ = ∑ i : Fin 6,
          ((if neutral i then (1 : ℂ) else 0) -
           (if neutral i then Δ i i else 0)) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hpoint i
      _ = ((Finset.univ.filter neutral).card : ℂ) - SN := by
        have hones : (∑ i : Fin 6, if neutral i then (1 : ℂ) else 0) =
            ((Finset.univ.filter neutral).card : ℂ) := by
          rw [← Finset.sum_filter]
          simp
        rw [Finset.sum_sub_distrib, hones]
        rfl
      _ = (m : ℂ) - SN := by
        rw [sixPlusNeutral_card_eq_fibreSum label]
  have hComplementEnergy :
      (∑ i : Fin 6, ∑ j : Fin 6,
        if ¬neutral i ∧ ¬neutral j then W i j * W j i else 0) =
        (8 : ℂ) * (e : ℂ) := by
    calc
      _ = (4 : ℂ) * labelledOpposite03Energy label D :=
        sixLabelled_plusWitness_complement_energy label D
      _ = (8 : ℂ) * (e : ℂ) := by
        rw [sixLabelled_opposite03Energy_eq_two_blockEnergy label D hD]
        ring
  have hEq : (6 : ℂ) - S = 2 * (m : ℂ) - 2 * SN + 8 * (e : ℂ) := by
    calc
      (6 : ℂ) - S = (W * W).trace := hTraceDefect.symm
      _ = 2 * (∑ i : Fin 6,
          if neutral i then (W * W) i i else 0) +
          (∑ i : Fin 6, ∑ j : Fin 6,
            if ¬neutral i ∧ ¬neutral j then W i j * W j i else 0) :=
              hTrace
      _ = 2 * (m : ℂ) - 2 * SN + 8 * (e : ℂ) := by
        rw [hNeutralDefect, hComplementEnergy]
        ring
  have hSigned : S - 2 * SN =
      (∑ i : Fin 6, if neutral i then -(Δ i i) else Δ i i) := by
    calc
      S - 2 * SN =
          (∑ i : Fin 6,
            (Δ i i - 2 * (if neutral i then Δ i i else 0))) := by
              simp [S, SN, Finset.sum_sub_distrib, Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hn : neutral i <;> simp [hn] <;> ring
  rw [← hSigned]
  linear_combination hEq

/-- Quantitative MAN-92 rigidity near the positive Pauli endpoint:
the complementary 00/11 energy determines the neutral dimension,
up to twelve times the original signed spectral slack. -/
theorem sixLabelled_exactHamming_positiveNearHalf_traceRigidity
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (epsilon : ℝ)
    (hc : 0 ≤ sixOrientedOppositeEnergyImbalance label D)
    (hnear : (1 / 2 : ℝ) - epsilon ≤
      sixOrientedOppositeEnergyImbalance label D) :
    |8 * sixTruthFibreBlockEnergy label D 0 3 -
        (6 - 2 * ((truthMultiplicity label 1 +
          truthMultiplicity label 2 : ℕ) : ℝ))| ≤
      12 * epsilon := by
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Δ : SixMat := 1 - W * W
  let neutral : Fin 6 → Prop := fun i => squarePlusNeutral (label i)
  let m : ℕ := truthMultiplicity label 1 + truthMultiplicity label 2
  let e : ℝ := sixTruthFibreBlockEnergy label D 0 3
  have hId := sixLabelled_plusWitness_traceDefect_signedIdentity
    label D hD
  change (6 : ℂ) = 2 * (m : ℂ) + 8 * (e : ℂ) +
    (∑ i : Fin 6, if neutral i then -(Δ i i) else Δ i i) at hId
  have hRearrange :
      (8 : ℂ) * (e : ℂ) - ((6 : ℂ) - 2 * (m : ℂ)) =
        -(∑ i : Fin 6, if neutral i then -(Δ i i) else Δ i i) := by
    linear_combination -hId
  have hMatrixBound := sixMatrix_signedDiagonalSum_norm_le_six Δ neutral
  have hNormBound :
      ‖(8 : ℂ) * (e : ℂ) - ((6 : ℂ) - 2 * (m : ℂ))‖ ≤
        6 * ‖Δ‖ := by
    rw [hRearrange, norm_neg]
    exact hMatrixBound
  have hRealEq :
      (8 : ℂ) * (e : ℂ) - ((6 : ℂ) - 2 * (m : ℂ)) =
        ((8 * e - (6 - 2 * (m : ℝ)) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hRealEq, Complex.norm_real, Real.norm_eq_abs] at hNormBound
  have hDefect := sixLabelled_exactHamming_positiveNearHalf_defect_norm_le
    label D hD hham epsilon hc hnear
  change ‖Δ‖ ≤ 2 * epsilon at hDefect
  change |8 * e - (6 - 2 * (m : ℝ))| ≤ 12 * epsilon
  linarith

end Neoplatonic.LTR
