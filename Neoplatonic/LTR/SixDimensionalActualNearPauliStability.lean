import Neoplatonic.LTR.SixDimensionalNearSaturatedPauliStability
import Neoplatonic.LTR.SixDimensionalExactHammingPauliSaturation
import Mathlib.Tactic

/-!
# LTR-MAN-141: actual six-dimensional residual Pauli stability near sharp overlap

MAN-139 proved quantitative real Gram bounds for scalar q,r,c
under nonnegative quadratic lengths, the Gram determinant, and
the simultaneous signed contraction budget.

The genuine labelled six-dimensional exact-Hamming Dirac
extremal system supplies precisely those inequalities on its
common two-dimensional residual Pauli matrices M,N. The real
mixed scalar is the original opposite-fibre energy imbalance
c=2(E03-E12), by MAN-84.

For every ε such that |c| >= 1/2-ε, the genuine residual obeys
  1/2-ε <= q+r <= 1/2+ε,
  (q-r)² <= 2ε,
  q+r+c <= 2ε or q+r-c <= 2ε.

These are necessary bounds for a genuine original 6D spectral
representation. They quantify the approaching rigidity of the
interior region near the MAN-138 forbidden endpoint.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Near the forbidden maximum absolute Pauli overlap, the two
actual residual quadratic lengths approach their saturated values,
and one signed residual quadratic energy becomes small. -/
theorem sixLabelled_exactHamming_nearHalf_realPauli_stability
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (ε : ℝ)
    (hnear : (1 / 2 : ℝ) - ε ≤
      |sixOrientedOppositeEnergyImbalance label D|) :
    ∃ S : TwoDirectionExtremalSystem SixH,
      ∃ hq : Orthonormal ℂ
        (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus),
        S.A = sixLabelledAOperator label D ∧
        S.B = sixLabelledBOperator label D ∧
        let M := S.sixDimResidualMatrixA hq (by simp)
        let N := S.sixDimResidualMatrixB hq (by simp)
        let q := pauliRealQuadratic M
        let r := pauliRealQuadratic N
        let c := pauliRealMixed M N
        ((1 / 2 : ℝ) - ε ≤ q + r ∧
          q + r ≤ (1 / 2 : ℝ) + ε) ∧
        (q - r) ^ 2 ≤ 2 * ε ∧
        (q + r + c ≤ 2 * ε ∨ q + r - c ≤ 2 * ε) := by
  obtain ⟨S, hq, hA, hB, _, _⟩ :=
    sixLabelled_exactHamming_oppositeEnergy_budget label D hD hham
  let M := S.sixDimResidualMatrixA hq (by simp)
  let N := S.sixDimResidualMatrixB hq (by simp)
  let q : ℝ := pauliRealQuadratic M
  let r : ℝ := pauliRealQuadratic N
  let c : ℝ := pauliRealMixed M N
  have htrA : LinearMap.trace ℂ SixH S.A.toLinearMap = 0 := by
    rw [hA]
    exact (sixLabelled_operatorTrace_zero label D).1
  have htrB : LinearMap.trace ℂ SixH S.B.toLinearMap = 0 := by
    rw [hB]
    exact (sixLabelled_operatorTrace_zero label D).2
  obtain ⟨hq0, hr0, hdet, hbudget⟩ :=
    S.sixDimResidual_realGram_cone hq (by simp) htrA htrB
  change 0 ≤ q at hq0
  change 0 ≤ r at hr0
  change c ^ 2 ≤ 4 * q * r at hdet
  change q + r + |c| ≤ 1 at hbudget
  have hreal : c = sixOrientedOppositeEnergyImbalance label D := by
    change (pauliMixed M N).re = _
    rw [sixLabelled_extremal_pauliMixed_eq_realImbalance
      label D hD S hq hA hB]
    simp
  have hnear' : (1 / 2 : ℝ) - ε ≤ |c| := by
    rw [hreal]
    exact hnear
  have hsum := realGram_nearHalf_sum_length_near_quarter
    q r c ε hq0 hr0 hdet hbudget hnear'
  have hdiff := realGram_nearHalf_length_difference_sq_le
    q r c ε hq0 hr0 hdet hbudget hnear'
  have hsigned := realGram_nearHalf_oneSignedEnergy_small
    q r c ε hbudget hnear'
  refine ⟨S, hq, hA, hB, ?_⟩
  change ((1 / 2 : ℝ) - ε ≤ q + r ∧
      q + r ≤ (1 / 2 : ℝ) + ε) ∧
    (q - r) ^ 2 ≤ 2 * ε ∧
    (q + r + c ≤ 2 * ε ∨ q + r - c ≤ 2 * ε)
  exact ⟨hsum, hdiff, hsigned⟩

end Neoplatonic.LTR
