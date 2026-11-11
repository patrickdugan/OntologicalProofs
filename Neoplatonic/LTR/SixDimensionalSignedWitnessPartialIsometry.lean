import Neoplatonic.LTR.SixDimensionalZeroNeutralBlockEquations
import Mathlib.Tactic

/-!
# LTR-MAN-94: actual saturated Hamming Dirac corner-neutral partial isometries

MAN-91 promotes the signed Hamming witnesses to involutions of the
actual six-dimensional complex Dirac commutator matrix. MAN-93
establishes the vanishing of the neutral truth-sector block.

The general MAN-94 full block identities therefore apply to these
genuine witness matrices, with no separate spectral assumptions.
For the positive sign, the neutral sector is truth atoms 01,10.
For the negative sign, the neutral sector is truth atoms 00,11.

Write C=I-Q, X=CWC, Y=CWQ. The true corner-neutral maps satisfy

    X² + YYᴴ = C,    XY=0,    YᴴY=Q.

The last equality proves Y is isometric on the complete neutral truth
fibre, including any repeated Hilbert coordinates. It is the exact
precondition for the dimension/rank calculation in the opposite-double
2+2 remaining patterns.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Every diagonal 0/1 truth-sector projection is Hermitian,
independently of how its truth fibres are repeated. -/
theorem sixTruthSectorProjection_isHermitian
    (label : Fin 6 → Fin 4)
    (sector : Fin 4 → Prop) [DecidablePred sector] :
    (sixTruthSectorProjection label sector).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  change IsSelfAdjoint
    (if sector (label i) then (1 : ℂ) else 0)
  by_cases hi : sector (label i) <;> simp [hi, IsSelfAdjoint]

/-- At 00↔11 saturation, the actual six-dimensional PLUS witness
has a corner block X and neutral-to-corner block Y that obey
the Hermitian partial-isometry equations in the same Dirac chart. -/
theorem sixLabelled_exactHamming_saturated03_partialIsometry
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
    let X := C * W * C
    let Y := C * W * Q
    X * X + Y * Y.conjTranspose = C ∧
      X * Y = 0 ∧ Y.conjTranspose * Y = Q := by
  dsimp only
  apply sixMatrix_hermitianInvolution_zeroNeutral_partialIsometry
  · exact sixLabelled_exactHamming_saturated03_trueMatrixPlus_involution
      label D hD hham h03 h12
  · exact sixLabelled_plusWitness_isHermitian label D hD
  · exact sixTruthSectorProjection_idempotent label squarePlusNeutral
  · exact sixTruthSectorProjection_W_zero label squarePlusNeutral _
      (sixLabelled_plusWitness_neutral_entry_zero label D)
  · exact sixTruthSectorProjection_isHermitian label squarePlusNeutral

/-- At 01↔10 saturation, the original six-dimensional MINUS
witness has the dual corner-neutral partial-isometry equations. -/
theorem sixLabelled_exactHamming_saturated12_partialIsometry
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
    let X := C * W * C
    let Y := C * W * Q
    X * X + Y * Y.conjTranspose = C ∧
      X * Y = 0 ∧ Y.conjTranspose * Y = Q := by
  dsimp only
  apply sixMatrix_hermitianInvolution_zeroNeutral_partialIsometry
  · exact sixLabelled_exactHamming_saturated12_trueMatrixMinus_involution
      label D hD hham h03 h12
  · exact sixLabelled_minusWitness_isHermitian label D hD
  · exact sixTruthSectorProjection_idempotent label squareMinusNeutral
  · exact sixTruthSectorProjection_W_zero label squareMinusNeutral _
      (sixLabelled_minusWitness_neutral_entry_zero label D)
  · exact sixTruthSectorProjection_isHermitian label squareMinusNeutral

end Neoplatonic.LTR
