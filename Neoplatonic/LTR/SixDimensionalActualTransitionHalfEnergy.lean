import Neoplatonic.LTR.SixDimensionalTransitionGramPositivity
import Neoplatonic.LTR.SixDimensionalSaturated03TransitionTrace
import Mathlib.Tactic

/-!
# LTR-MAN-119: genuine opposite-double neutral row half-energy

MAN-117 proves the actual six-coordinate transition trace table
of the saturated 2+2 witness is doubly stochastic. MAN-118
certifies that any individual output/neutral transition trace
is the complex embedding of a nonnegative real Gram energy.

Combining these yields a genuine six-dimensional half-energy
dichotomy, without assuming an artificial unitary basis.

The final no-go will relate these squared transition energies
to the operator norms of the original two coordinate commutators.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The actual opposite-double saturated neutral exchange
distributes unit trace between two nonnegative transitions out
of the 00 corner fibre, with one at most one half. -/
theorem sixLabelled_exactHamming_saturated03_transitionHalfEnergy
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    let Y := C * W * Q
    let P0 := sixTruthFibreProjection label 0
    let N1 := sixTruthFibreProjection label 1
    let N2 := sixTruthFibreProjection label 2
    ∃ a b : ℝ,
      0 ≤ a ∧ 0 ≤ b ∧
      sixMatrix_transitionTrace P0 Y N1 = (a : ℂ) ∧
      sixMatrix_transitionTrace P0 Y N2 = (b : ℂ) ∧
      a + b = 1 ∧
      (a ≤ (1 / 2 : ℝ) ∨ b ≤ (1 / 2 : ℝ)) := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let Y : SixMat := C * W * Q
  let P0 : SixMat := sixTruthFibreProjection label 0
  let N1 : SixMat := sixTruthFibreProjection label 1
  let N2 : SixMat := sixTruthFibreProjection label 2
  change ∃ a b : ℝ,
    0 ≤ a ∧ 0 ≤ b ∧
    sixMatrix_transitionTrace P0 Y N1 = (a : ℂ) ∧
    sixMatrix_transitionTrace P0 Y N2 = (b : ℂ) ∧
    a + b = 1 ∧
    (a ≤ (1 / 2 : ℝ) ∨ b ≤ (1 / 2 : ℝ))
  have hP0id : P0 * P0 = P0 := by
    simpa only [P0, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label
        (fun u : Fin 4 => u = 0))
  have hN1id : N1 * N1 = N1 := by
    simpa only [N1, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label
        (fun u : Fin 4 => u = 1))
  have hN2id : N2 * N2 = N2 := by
    simpa only [N2, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label
        (fun u : Fin 4 => u = 2))
  have hP0H : P0.IsHermitian := by
    simpa only [P0, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label
        (fun u : Fin 4 => u = 0))
  have hN1H : N1.IsHermitian := by
    simpa only [N1, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label
        (fun u : Fin 4 => u = 1))
  have hN2H : N2.IsHermitian := by
    simpa only [N2, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label
        (fun u : Fin 4 => u = 2))
  obtain ⟨a, ha, hta⟩ :=
    sixMatrix_transitionTrace_nonnegativeReal
      P0 N1 Y hP0id hN1id hP0H hN1H
  obtain ⟨b, hb, htb⟩ :=
    sixMatrix_transitionTrace_nonnegativeReal
      P0 N2 Y hP0id hN2id hP0H hN2H
  change sixMatrix_transitionTrace P0 Y N1 = (a : ℂ) at hta
  change sixMatrix_transitionTrace P0 Y N2 = (b : ℂ) at htb
  have hRow : sixMatrix_transitionTrace P0 Y N1 +
      sixMatrix_transitionTrace P0 Y N2 = (1 : ℂ) := by
    have h :=
      (sixLabelled_exactHamming_saturated03_oppositeDouble_transitionTrace
        label D hsurj hD hham h03 h12).1.1
    change sixMatrix_transitionTrace P0 Y N1 +
      sixMatrix_transitionTrace P0 Y N2 = (1 : ℂ) at h
    exact h
  have hSum : a + b = (1 : ℝ) := by
    apply Complex.ofReal_injective
    have h : ((a + b : ℝ) : ℂ) = 1 := by
      rw [Complex.ofReal_add, ← hta, ← htb]
      exact hRow
    simpa using h
  exact ⟨a, b, ha, hb, hta, htb, hSum,
    twoTransitionNonnegative_rowHalf a b ha hb hSum⟩

end Neoplatonic.LTR
