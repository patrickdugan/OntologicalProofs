import Neoplatonic.LTR.SixDimensionalSaturated03ActualNormNoGo
import Neoplatonic.LTR.SixDimensionalTruthRelabelSaturation
import Mathlib.Tactic

/-!
# LTR-MAN-136: no pure signed Hamming saturation in six Hilbert dimensions

MAN-135 excludes exact Hamming with pure positive saturation of
the opposite 00-to-11 Dirac block. Truth translation by the first
Boolean bit preserves all six exact Connes distances and the actual
Hermitian D. It interchanges opposite truth pairs (00,11) and (01,10).

The formerly pure negative saturation therefore becomes exactly
MAN-135's impossible positive saturation, in the same six-coordinate
Hilbert space. This module excludes both orientations and joins them
into a single pure-saturation impossibility theorem.

Maximal residual Pauli overlap and every non-saturated exact-Hamming
configuration require separately discharged premises.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The original six-dimensional Hermitian Dirac matrix cannot
realize exact Hamming distances with pure 01/10 saturation,
because a Boolean-square translation converts it to the already
excluded pure 00/11 saturation. -/
theorem sixLabelled_exactHamming_saturated12_actualNorm_impossible
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = 0)
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    False := by
  let τ := twoBitSquareTranslation 1
  obtain ⟨ht0, ht1, ht2, ht3⟩ := twoBitSquareTranslation_one_values
  have hsurj' : Function.Surjective (τ ∘ label) := by
    intro u
    obtain ⟨i, hi⟩ := hsurj (τ.symm u)
    refine ⟨i, ?_⟩
    change τ (label i) = u
    rw [hi, Equiv.apply_symm_apply]
  have hham' :
      ∀ u v : Fin 4,
        sixLabelledConnesDistance (τ ∘ label) D u v =
          (twoBitSquareHamming u v : ℝ≥0∞) :=
    sixLabelled_exactHamming_truthTranslation label D 1 hham
  have he03' :
      sixTruthFibreBlockEnergy (τ ∘ label) D 0 3 =
        (1 / 4 : ℝ) := by
    have h := sixTruthFibreBlockEnergy_truthEquiv τ label D 1 2
    rw [ht1, ht2] at h
    exact h.trans h12
  have he12' :
      sixTruthFibreBlockEnergy (τ ∘ label) D 1 2 = 0 := by
    have h := sixTruthFibreBlockEnergy_truthEquiv τ label D 0 3
    rw [ht0, ht3] at h
    exact h.trans h03
  exact sixLabelled_exactHamming_saturated03_actualNorm_impossible
    (τ ∘ label) D hsurj' hD hham' he03' he12'

/-- Neither of the two pure opposite-corner saturation signs can
occur for an exact two-bit Hamming six-dimensional spectral metric. -/
theorem sixLabelled_exactHamming_pureSaturation_impossible
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hpure :
      (sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ) ∧
        sixTruthFibreBlockEnergy label D 1 2 = 0) ∨
      (sixTruthFibreBlockEnergy label D 0 3 = 0 ∧
        sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ))) :
    False := by
  rcases hpure with ⟨h03, h12⟩ | ⟨h03, h12⟩
  · exact sixLabelled_exactHamming_saturated03_actualNorm_impossible
      label D hsurj hD hham h03 h12
  · exact sixLabelled_exactHamming_saturated12_actualNorm_impossible
      label D hsurj hD hham h03 h12

end Neoplatonic.LTR
