import Neoplatonic.LTR.SixDimensionalFullExchangeSandwichCancellation
import Neoplatonic.LTR.SixDimensionalOverneutralQuartetFullRank
import Neoplatonic.LTR.SixDimensionalOverneutralExchangeRank
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-187: exact original 01↔10 signed Dirac corner extinction

Let the complex six-dimensional Hermitian Dirac operator D represent
the two-bit exact Connes Hamming metric with singleton 01/10
truth fibres. For its negative witness W-=A−B, let Q be the
00/11 neutral truth-sector projector, C=I−Q, X=CWC, Y=CWQ.

MAN-180/184 proves the original cubic neutral compression
    Yᴴ X Y=0.
MAN-174/185 proves rank(W)=4 and rank(Y)=rank(C)=2
from the exact Hamming eigenquartet.
MAN-186 gives a genuine original-coordinate matrix R with YR=C.
Since C is Hermitian and X=CXC, the cubic sandwich vanishes only if
    X=0.

This removes the entire original 01↔10 active signed corner
throughout the non-saturated interior, without assuming any Pauli
endpoint, gauge, or singular-vector normal form. The resulting
opposite Dirac block energy constraint follows in MAN-188.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The actual original negative signed Hamming witness
has zero complete active 01/10 corner when both active truth
fibres are singleton and all Connes Hamming distances are exact. -/
theorem sixLabelled_exactHamming_overneutral_minus_activeCorner_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hm1 : truthMultiplicity label 1 = 1)
    (hm2 : truthMultiplicity label 2 = 1) :
    let W := labelledSquareA label D - labelledSquareB label D
    let Q := sixTruthSectorProjection label squareMinusNeutral
    let C : SixMat := 1 - Q
    C * W * C = 0 := by
  dsimp only
  let W : SixMat := labelledSquareA label D - labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squareMinusNeutral
  let C : SixMat := 1 - Q
  let X : SixMat := C * W * C
  let Y : SixMat := C * W * Q
  change X = 0
  have hQ2 : Q * Q = Q :=
    sixTruthSectorProjection_idempotent label squareMinusNeutral
  have hQH : Q.IsHermitian :=
    sixTruthSectorProjection_isHermitian label squareMinusNeutral
  have hCH : C.IsHermitian := by
    change (1 - Q).conjTranspose = 1 - Q
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hQH.eq]
  have hC2 : C * C = C := by
    dsimp [C]
    calc
      (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q := by noncomm_ring
      _ = 1 - Q := by rw [hQ2]; abel
  have hCY : C * Y = Y := by
    change C * (C * W * Q) = C * W * Q
    calc
      C * (C * W * Q) = (C * C) * W * Q := by noncomm_ring
      _ = C * W * Q := by rw [hC2]
  have hCX : C * X * C = X := by
    change C * (C * W * C) * C = C * W * C
    calc
      C * (C * W * C) * C = (C * C) * W * (C * C) := by
        noncomm_ring
      _ = C * W * C := by rw [hC2]
  have hSand :=
    sixLabelled_exactHamming_overneutral_minus_cubic_exchange_sandwich_zero
      label D hD hham hm1 hm2
  change Y.conjTranspose * X * Y = 0 at hSand
  have hRankY :=
    sixLabelled_exactHamming_overneutral_minus_exchange_rank_two
      label D hD hham hm1 hm2
  change Y.rank = 2 at hRankY
  have hRankC : C.rank = 2 := by
    change (1 - Q : SixMat).rank = 2
    rw [sixMinusNeutral_complement_eq_plusNeutral,
      sixPlusNeutral_projection_rank_eq_fibreSum label, hm1, hm2]
  have hRankEq : Y.rank = C.rank := by
    rw [hRankY, hRankC]
  exact sixMatrix_fullRankExchange_sandwich_zero_forces_corner_zero
    C X Y hCH hCY hCX hRankEq hSand

end Neoplatonic.LTR
