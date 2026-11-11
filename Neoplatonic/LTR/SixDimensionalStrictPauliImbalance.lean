import Neoplatonic.LTR.SixDimensionalPositiveMaxImbalanceNoGo
import Neoplatonic.LTR.SixDimensionalTruthRelabelSaturation
import Neoplatonic.LTR.SixDimensionalExactHammingPauliSaturation
import Mathlib.Tactic

/-!
# LTR-MAN-138: strict residual Pauli overlap under exact six-dimensional Hamming

MAN-85 established the universal necessary condition
  |E03 - E12| <= 1/4.
MAN-137 excludes the positive equality endpoint using the actual
signed involution and its trace. Boolean-square truth translation
exchanges the two opposite energy blocks while preserving the full
Connes Hamming metric and the same six-dimensional Hermitian D.

Both equality endpoints are therefore excluded, sharpening MAN-85 to
the strict inequality
  |E03 - E12| < 1/4
and hence |c| < 1/2 for the original oriented residual Pauli mixed
coefficient c=2(E03-E12).

This is a strict necessary condition for any genuine six-dimensional
exact Hamming spectral representation. It does not settle whether
non-saturated six-dimensional representations exist.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Negative maximal Pauli imbalance is the positive obstruction
after complementing the first Boolean coordinate of the truth square. -/
theorem sixLabelled_exactHamming_maxNegativeImbalance_impossible
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hsign : sixTruthFibreBlockEnergy label D 1 2 -
      sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ)) :
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
  have hEnergy03 :
      sixTruthFibreBlockEnergy (τ ∘ label) D 0 3 =
        sixTruthFibreBlockEnergy label D 1 2 := by
    have h := sixTruthFibreBlockEnergy_truthEquiv τ label D 1 2
    rwa [ht1, ht2] at h
  have hEnergy12 :
      sixTruthFibreBlockEnergy (τ ∘ label) D 1 2 =
        sixTruthFibreBlockEnergy label D 0 3 := by
    have h := sixTruthFibreBlockEnergy_truthEquiv τ label D 0 3
    rwa [ht0, ht3] at h
  have hsign' :
      sixTruthFibreBlockEnergy (τ ∘ label) D 0 3 -
        sixTruthFibreBlockEnergy (τ ∘ label) D 1 2 =
          (1 / 4 : ℝ) := by
    rw [hEnergy03, hEnergy12]
    exact hsign
  exact sixLabelled_exactHamming_maxPositiveImbalance_impossible
    (τ ∘ label) D hsurj' hD hham' hsign'

/-- The sharp MAN-85 quarter-bound is strict for every faithful
six-dimensional Hermitian Dirac representation of the exact
two-bit Connes Hamming metric. -/
theorem sixLabelled_exactHamming_oppositeEnergyDiff_abs_lt_quarter
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    |sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2| < (1 / 4 : ℝ) := by
  have hle := sixLabelled_exactHamming_oppositeEnergyDiff_abs_le_quarter
    label D hD hham
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · rcases le_total 0 (sixTruthFibreBlockEnergy label D 0 3 -
        sixTruthFibreBlockEnergy label D 1 2) with hpos | hneg
    · have hposEq : sixTruthFibreBlockEnergy label D 0 3 -
        sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ) := by
        rwa [abs_of_nonneg hpos] at heq
      exact (sixLabelled_exactHamming_maxPositiveImbalance_impossible
        label D hsurj hD hham hposEq).elim
    · have hnegEq : sixTruthFibreBlockEnergy label D 1 2 -
        sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ) := by
        rw [abs_of_nonpos hneg] at heq
        linarith
      exact (sixLabelled_exactHamming_maxNegativeImbalance_impossible
        label D hsurj hD hham hnegEq).elim

/-- In the original residual Pauli convention c=2(E03-E12),
all six-dimensional exact-Hamming representations have strict
mixed real coefficient magnitude below one half. -/
theorem sixLabelled_exactHamming_realPauliMixed_strict_half
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    |sixOrientedOppositeEnergyImbalance label D| < (1 / 2 : ℝ) := by
  have h := sixLabelled_exactHamming_oppositeEnergyDiff_abs_lt_quarter
    label D hsurj hD hham
  dsimp [sixOrientedOppositeEnergyImbalance]
  rw [abs_mul]
  norm_num at h ⊢
  linarith

end Neoplatonic.LTR
