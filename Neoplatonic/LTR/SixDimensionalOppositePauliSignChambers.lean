import Neoplatonic.LTR.SixDimensionalOverneutralPauliSign
import Neoplatonic.LTR.SixDimensionalUniformSignedPauliMargin
import Neoplatonic.LTR.SixDimensionalNegativeNearHalfDefect
import Mathlib.Tactic

/-!
# LTR-MAN-182: opposing real Pauli sign chambers from truth multiplicity

MAN-181 shows that the *original* Pauli mixed coefficient
c=2(E03-E12) is nonnegative throughout the interior whenever
the truth fibres 01 and 10 are singleton.

First-bit truth translation swaps the two opposite diagonals,
preserves every exact-Hamming Connes distance, and sends c to -c.
Therefore singleton 00 and 11 truth fibres force c<=0.

Combining the sign laws with MAN-171's uniform endpoint collar gives
two disjoint (except for c=0) necessary feasibility chambers:

  m01=m10=1:      0 <= c < 62/125
  m00=m11=1: -62/125 < c <= 0.

No Pauli saturation or special choice of original complex
six-dimensional Dirac basis is assumed.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A faithful six-dimensional chart whose 00/11 opposite
truth fibres are singleton has nonpositive original real
Pauli overlap, by the exact Boolean-square first-bit symmetry. -/
theorem sixLabelled_exactHamming_opposite00and11Singletons_pauliImbalance_nonpos
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm0 : truthMultiplicity label 0 = 1)
    (hm3 : truthMultiplicity label 3 = 1) :
    sixOrientedOppositeEnergyImbalance label D ≤ 0 := by
  let tau := twoBitSquareTranslation 1
  obtain ⟨ht0, ht1, ht2, ht3⟩ :=
    twoBitSquareTranslation_one_values
  have hm1' : truthMultiplicity (tau ∘ label) 1 = 1 := by
    have h := sixTruthMultiplicity_truthEquiv tau label 0
    rw [ht0] at h
    exact h.trans hm0
  have hm2' : truthMultiplicity (tau ∘ label) 2 = 1 := by
    have h := sixTruthMultiplicity_truthEquiv tau label 3
    rw [ht3] at h
    exact h.trans hm3
  have hham' : ∀ u v : Fin 4,
      sixLabelledConnesDistance (tau ∘ label) D u v =
        (twoBitSquareHamming u v : ℝ≥0∞) :=
    sixLabelled_exactHamming_truthTranslation label D 1 hham
  have hPos :=
    sixLabelled_exactHamming_overneutral_pauliImbalance_nonneg
      (tau ∘ label) D hD hham' hm1' hm2'
  rw [sixOrientedOppositeEnergyImbalance_translationOne_neg] at hPos
  linarith

/-- The singleton 01/10 stratum lies inside the closed positive
signed Pauli half-axis and MAN-171's strict uniform collar. -/
theorem sixLabelled_exactHamming_opposite01and10Singletons_positivePauliChamber
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1) :
    0 ≤ sixOrientedOppositeEnergyImbalance label D ∧
      sixOrientedOppositeEnergyImbalance label D <
        (62 / 125 : ℝ) := by
  have hPos := sixLabelled_exactHamming_overneutral_pauliImbalance_nonneg
    label D hD hham hm1 hm2
  have hAbs :=
    sixLabelled_exactHamming_realPauliMixed_abs_lt_62over125
      label D hsurj hD hham
  exact ⟨hPos, (abs_lt.mp hAbs).2⟩

/-- The mirror 00/11 singleton stratum is confined to the
nonpositive interior Pauli half-axis by the same original
Dirac truth-translation symmetry. -/
theorem sixLabelled_exactHamming_opposite00and11Singletons_negativePauliChamber
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm0 : truthMultiplicity label 0 = 1)
    (hm3 : truthMultiplicity label 3 = 1) :
    -(62 / 125 : ℝ) <
        sixOrientedOppositeEnergyImbalance label D ∧
      sixOrientedOppositeEnergyImbalance label D ≤ 0 := by
  have hNeg :=
    sixLabelled_exactHamming_opposite00and11Singletons_pauliImbalance_nonpos
      label D hD hham hm0 hm3
  have hAbs :=
    sixLabelled_exactHamming_realPauliMixed_abs_lt_62over125
      label D hsurj hD hham
  exact ⟨(abs_lt.mp hAbs).1, hNeg⟩

end Neoplatonic.LTR
