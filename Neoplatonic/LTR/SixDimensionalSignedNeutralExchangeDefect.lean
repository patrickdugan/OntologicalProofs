import Neoplatonic.LTR.SixDimensionalSignedOppositeGramCornerBridge
import Neoplatonic.LTR.SixDimensionalSignedCornerComplementaryProjections
import Mathlib.Tactic

/-!
# LTR-MAN-102: exact neutral-exchange defect equation in the true Dirac chart

MAN-97 proves X²+YYᴴ=C for the saturated signed Hamming witness.
MAN-100 identifies X² with the two Gram products of the genuine
surviving Dirac opposite block. This module composes both kernel
results directly in the original six-dimensional coordinates:

  YYᴴ + TTᴴ + TᴴT = C.

The equality is the exact algebraic bridge to a unitary normal form:
the neutral exchange fills the two-dimensional orthogonal complement
of the surviving rank-one opposite channel on each truth-atom fibre.

This result by itself does not select bases or prove the final
coordinate-commutator norm contradiction.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Positive 00/11 saturation: the neutral exchange and both
oriented scaled Dirac Gram matrices sum to the true corner
projection, in the given six-dimensional labelled chart. -/
theorem sixLabelled_exactHamming_saturated03_neutralExchange_defect
    (label : Fin 6 → Fin 4) (D : SixMat)
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
    let T := ((2 : ℂ) * Complex.I) • sixTruthFibreBlock label D 0 3
    Y * Y.conjTranspose +
      T * T.conjTranspose + T.conjTranspose * T = C := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let X : SixMat := C * W * C
  let Y : SixMat := C * W * Q
  let T : SixMat := ((2 : ℂ) * Complex.I) •
    sixTruthFibreBlock label D 0 3
  change Y * Y.conjTranspose +
    T * T.conjTranspose + T.conjTranspose * T = C
  have hpart :
      X * X + Y * Y.conjTranspose = C := by
    have h :=
      (sixLabelled_exactHamming_saturated03_cornerOrthogonalSplit
        label D hD hham h03 h12).2.2.2.2.1
    change X * X + Y * Y.conjTranspose = C at h
    exact h
  have hX :
      X * X = T * T.conjTranspose + T.conjTranspose * T := by
    have h :=
      sixLabelled_exactHamming_saturated03_cornerSquare_oppositeGram
        label D hD
    change X * X = T * T.conjTranspose + T.conjTranspose * T at h
    exact h
  rw [hX] at hpart
  calc
    Y * Y.conjTranspose +
        T * T.conjTranspose + T.conjTranspose * T =
      (T * T.conjTranspose + T.conjTranspose * T) +
        Y * Y.conjTranspose := by abel
    _ = C := hpart

/-- Negative 01/10 saturation has the corresponding exact
neutral-exchange defect equation with the -2i-scaled original
opposite Dirac block. -/
theorem sixLabelled_exactHamming_saturated12_neutralExchange_defect
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = 0)
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    let W := labelledSquareA label D - labelledSquareB label D
    let Q := sixTruthSectorProjection label squareMinusNeutral
    let C := (1 - Q : SixMat)
    let Y := C * W * Q
    let T := ((-2 : ℂ) * Complex.I) • sixTruthFibreBlock label D 1 2
    Y * Y.conjTranspose +
      T * T.conjTranspose + T.conjTranspose * T = C := by
  dsimp only
  let W : SixMat := labelledSquareA label D - labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squareMinusNeutral
  let C : SixMat := 1 - Q
  let X : SixMat := C * W * C
  let Y : SixMat := C * W * Q
  let T : SixMat := ((-2 : ℂ) * Complex.I) •
    sixTruthFibreBlock label D 1 2
  change Y * Y.conjTranspose +
    T * T.conjTranspose + T.conjTranspose * T = C
  have hpart :
      X * X + Y * Y.conjTranspose = C := by
    have h :=
      (sixLabelled_exactHamming_saturated12_cornerOrthogonalSplit
        label D hD hham h03 h12).2.2.2.2.1
    change X * X + Y * Y.conjTranspose = C at h
    exact h
  have hX :
      X * X = T * T.conjTranspose + T.conjTranspose * T := by
    have h :=
      sixLabelled_exactHamming_saturated12_cornerSquare_oppositeGram
        label D hD
    change X * X = T * T.conjTranspose + T.conjTranspose * T at h
    exact h
  rw [hX] at hpart
  calc
    Y * Y.conjTranspose +
        T * T.conjTranspose + T.conjTranspose * T =
      (T * T.conjTranspose + T.conjTranspose * T) +
        Y * Y.conjTranspose := by abel
    _ = C := hpart

end Neoplatonic.LTR
