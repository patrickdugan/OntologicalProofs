import Neoplatonic.LTR.SixDimensionalSingleton11NeutralRowExtinction
import Neoplatonic.LTR.SixDimensionalSaturated03Singleton00NoGo
import Neoplatonic.LTR.SixDimensionalTriple11ProbeHammingNoGo
import Neoplatonic.LTR.SixDimensionalSaturatedFibreClassification
import Mathlib.Tactic

/-!
# LTR-MAN-112: reflected triple-fibre saturated Hamming no-go

MAN-110 proves the positive saturated witness W+=A+B has zero
neutral-exchange row at truth atom 11 when its fibre is a singleton.

The original signed-Hamming coefficient between 11 and each neutral
truth atom is -i, so the original Hermitian Dirac couplings vanish.
MAN-111's mirrored probe (2,3,3,0) then contradicts an exact Hamming
edge of length one.

Consequently pure 03 saturation in a faithful six-dimensional chart
forces the two opposite truth fibres to be doubled and both neutral
fibres to be singleton. This leaves only the (2,1,1,2) opposite-double
pattern among the positive saturated candidates.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Truth fibre 11 is orthogonal to the positive witness neutral
sector 01/10 for every six-dimensional labelling. -/
theorem sixPlusNeutral_fibre11_orthogonal
    (label : Fin 6 → Fin 4) :
    sixTruthFibreProjection label 3 *
      sixTruthSectorProjection label squarePlusNeutral = 0 := by
  ext i j
  simp only [sixTruthFibreProjection, sixTruthSectorProjection,
    Matrix.diagonal_mul]
  by_cases hi : label i = 3
  · simp [hi, squarePlusNeutral, Matrix.diagonal_apply]
  · simp [hi]

/-- On a 11-to-neutral block, W+=i[D,P+Q] has coefficient -i. -/
theorem sixPlusWitness_11neutral_entry
    (label : Fin 6 → Fin 4) (D : SixMat)
    (i j : Fin 6)
    (hi : label i = 3)
    (hj : squarePlusNeutral (label j)) :
    (labelledSquareA label D + labelledSquareB label D) i j =
      -Complex.I * D i j := by
  rcases hj with h1 | h2
  · simp [Matrix.add_apply, labelledSquareA, labelledSquareB,
      squareTruthBitP, squareTruthBitQ, hi, h1] <;> ring
  · simp [Matrix.add_apply, labelledSquareA, labelledSquareB,
      squareTruthBitP, squareTruthBitQ, hi, h2] <;> ring

/-- Singleton-11 row extinction eliminates both directions of
all original Dirac couplings between 11 and neutral atoms 01/10. -/
theorem sixLabelled_exactHamming_saturated03_singleton11_noNeutralDirac
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (hMult : truthMultiplicity label 3 = 1) :
    ∀ i j : Fin 6, squareTriple11Bad (label i) (label j) →
      D i j = 0 := by
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let R : SixMat := sixTruthFibreProjection label 3
  have hRY : R * ((1 - Q) * W * Q) = 0 := by
    have h := sixLabelled_exactHamming_saturated03_singleton11_neutralRow_zero
      label D hD hham h03 h12 hMult
    change R * ((1 - Q) * W * Q) = 0 at h
    exact h
  have hRQ : R * Q = 0 :=
    sixPlusNeutral_fibre11_orthogonal label
  have hRWQ : R * W * Q = 0 :=
    sixMatrix_neutralRow_zero_implies_fullRow_zero R Q W hRQ hRY
  have hforward :
      ∀ i j : Fin 6, label i = 3 →
        squarePlusNeutral (label j) → D i j = 0 := by
    intro i j hi hj
    have hmatrix : (R * W * Q) i j = 0 := by rw [hRWQ]; rfl
    have hWzero : W i j = 0 := by
      simpa [R, Q, sixTruthFibreProjection,
        sixTruthSectorProjection, Matrix.diagonal_mul,
        Matrix.mul_diagonal, hi, hj] using hmatrix
    have hcoef : W i j = -Complex.I * D i j :=
      sixPlusWitness_11neutral_entry label D i j hi hj
    rw [hcoef] at hWzero
    exact (mul_eq_zero.mp hWzero).resolve_left (by norm_num)
  intro i j hbad
  change (label i = 3 ∧
      (label j = 1 ∨ label j = 2)) ∨
    (label j = 3 ∧
      (label i = 1 ∨ label i = 2)) at hbad
  rcases hbad with ⟨hi, hj⟩ | ⟨hj, hi⟩
  · exact hforward i j hi hj
  · have hreverse : D j i = 0 := hforward j i hj hi
    rw [hD i j, hreverse]
    simp

/-- The (3,1,1,1) candidate cannot realize pure positive 03
saturation with exact six-dimensional Hamming Connes distances. -/
theorem sixLabelled_exactHamming_saturated03_singleton11_impossible
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (hMult : truthMultiplicity label 3 = 1) :
    False := by
  exact sixLabelled_exactHamming_saturated03_zeroNeutral11Rows_impossible
    label D hD hham h03 h12
    (sixLabelled_exactHamming_saturated03_singleton11_noNeutralDirac
      label D hD hham h03 h12 hMult)

/-- Combining both endpoint no-go theorems with MAN-92's neutral
singleton classification leaves only the (2,1,1,2) fibre pattern
for *pure positive* saturation in a faithful six-dimensional chart. -/
theorem sixLabelled_exactHamming_saturated03_onlyOppositeDoubles
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    truthMultiplicity label 0 = 2 ∧
      truthMultiplicity label 1 = 1 ∧
      truthMultiplicity label 2 = 1 ∧
      truthMultiplicity label 3 = 2 := by
  obtain ⟨hm1, hm2⟩ :=
    sixLabelled_saturated03_neutralFibres_singleton
      label D hsurj hD hham h03 h12
  have hsum : truthMultiplicity label 0 +
      truthMultiplicity label 1 +
      truthMultiplicity label 2 +
      truthMultiplicity label 3 = 6 := by
    simpa only [Fin.sum_univ_four] using truthMultiplicity_sum label
  have hp0 := truthMultiplicity_pos label hsurj 0
  have hp3 := truthMultiplicity_pos label hsurj 3
  have hnot0 : truthMultiplicity label 0 ≠ 1 := by
    intro h
    exact (sixLabelled_exactHamming_saturated03_singleton00_impossible
      label D hD hham h03 h12 h).elim
  have hnot3 : truthMultiplicity label 3 ≠ 1 := by
    intro h
    exact (sixLabelled_exactHamming_saturated03_singleton11_impossible
      label D hD hham h03 h12 h).elim
  omega

end Neoplatonic.LTR
