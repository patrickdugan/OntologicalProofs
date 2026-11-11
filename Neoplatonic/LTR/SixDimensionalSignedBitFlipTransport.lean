import Neoplatonic.LTR.SixDimensionalRealPauliDefectLeakage
import Neoplatonic.LTR.SixDimensionalTruthRelabelSaturation
import Mathlib.Tactic

/-!
# LTR-MAN-148: first Boolean bit translation exchanges signed witnesses

The Boolean-square isometry τ=translation by 01 flips the first
coordinate bit and preserves the second. On any actual labelled
complex six-dimensional Dirac matrix D, it sends

  A(τ ∘ label,D) = -A(label,D),
  B(τ ∘ label,D) = B(label,D),
  W_+(τ ∘ label,D) = -W_-(label,D).

Its plus-neutral sector equals the original minus-neutral sector.
All formulas hold before spectral saturation, on the original
Hilbert coordinate basis, with no canonical U(2) chart.
-/

namespace Neoplatonic.LTR

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Flipping the first truth bit complements its 0/1 value. -/
theorem squareTruthBitP_translationOne (u : Fin 4) :
    squareTruthBitP (twoBitSquareTranslation 1 u) =
      (1 : ℂ) - squareTruthBitP u := by
  obtain ⟨h0, h1, h2, h3⟩ := twoBitSquareTranslation_one_values
  fin_cases u <;>
    norm_num [h0, h1, h2, h3, squareTruthBitP]

/-- The second truth bit survives translation by the first. -/
theorem squareTruthBitQ_translationOne (u : Fin 4) :
    squareTruthBitQ (twoBitSquareTranslation 1 u) =
      squareTruthBitQ u := by
  obtain ⟨h0, h1, h2, h3⟩ := twoBitSquareTranslation_one_values
  fin_cases u <;>
    norm_num [h0, h1, h2, h3, squareTruthBitQ]

/-- The translation exchanges the plus and minus neutral sectors. -/
theorem squarePlusNeutral_translationOne_iff (u : Fin 4) :
    squarePlusNeutral (twoBitSquareTranslation 1 u) ↔
      squareMinusNeutral u := by
  fin_cases u <;>
    decide

/-- The first imaginary coordinate commutator changes sign when
its truth bit is complemented, for the same original Dirac matrix. -/
theorem sixLabelled_firstCoordinate_translationOne
    (label : Fin 6 → Fin 4) (D : SixMat) :
    labelledSquareA (twoBitSquareTranslation 1 ∘ label) D =
      -(labelledSquareA label D) := by
  ext i j
  change Complex.I *
    (squareTruthBitP (twoBitSquareTranslation 1 (label j)) -
      squareTruthBitP (twoBitSquareTranslation 1 (label i))) * D i j =
      -(Complex.I *
        (squareTruthBitP (label j) - squareTruthBitP (label i)) * D i j)
  rw [squareTruthBitP_translationOne, squareTruthBitP_translationOne]
  ring

/-- The second Dirac coordinate commutator remains unchanged. -/
theorem sixLabelled_secondCoordinate_translationOne
    (label : Fin 6 → Fin 4) (D : SixMat) :
    labelledSquareB (twoBitSquareTranslation 1 ∘ label) D =
      labelledSquareB label D := by
  ext i j
  change Complex.I *
    (squareTruthBitQ (twoBitSquareTranslation 1 (label j)) -
      squareTruthBitQ (twoBitSquareTranslation 1 (label i))) * D i j =
      Complex.I *
        (squareTruthBitQ (label j) - squareTruthBitQ (label i)) * D i j
  rw [squareTruthBitQ_translationOne, squareTruthBitQ_translationOne]

/-- The plus signed witness in the translated square is the
negative of the true minus signed witness in the original chart. -/
theorem sixLabelled_plusWitness_translationOne_eq_negMinus
    (label : Fin 6 → Fin 4) (D : SixMat) :
    labelledSquareA (twoBitSquareTranslation 1 ∘ label) D +
      labelledSquareB (twoBitSquareTranslation 1 ∘ label) D =
      -(labelledSquareA label D - labelledSquareB label D) := by
  rw [sixLabelled_firstCoordinate_translationOne,
      sixLabelled_secondCoordinate_translationOne]
  abel

/-- The neutral projection in the translated positive signed
chart is the original neutral projection for the minus witness. -/
theorem sixTruthPlusNeutralProjection_translationOne
    (label : Fin 6 → Fin 4) :
    sixTruthSectorProjection (twoBitSquareTranslation 1 ∘ label)
      squarePlusNeutral =
      sixTruthSectorProjection label squareMinusNeutral := by
  unfold sixTruthSectorProjection
  congr 1
  funext i
  simp only [Function.comp_apply]
  by_cases h : squareMinusNeutral (label i)
  · have hp :
        squarePlusNeutral (twoBitSquareTranslation 1 (label i)) :=
      (squarePlusNeutral_translationOne_iff (label i)).2 h
    simp [h, hp]
  · have hp :
        ¬squarePlusNeutral (twoBitSquareTranslation 1 (label i)) := by
          intro hp
          exact h ((squarePlusNeutral_translationOne_iff (label i)).1 hp)
    simp [h, hp]

end Neoplatonic.LTR
