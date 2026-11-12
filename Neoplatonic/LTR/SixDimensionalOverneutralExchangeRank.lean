import Neoplatonic.LTR.SixDimensionalOverneutralMinusCubic
import Neoplatonic.LTR.SixDimensionalOverneutralSignedRank
import Neoplatonic.LTR.SixDimensionalNonSaturatedCornerDefect
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-184: cubic neutral-to-corner cancellation and sharp exchange-rank gate

Write a Hermitian complex 6×6 signed witness as W with an orthogonal
neutral projector Q, complementary active projector C=I-Q, compressed
active block X=CWC and exchange Y=CWQ.

For QWQ=0 and W³=W the true neutral compression of the cubic relation is
  Yᴴ X Y = 0.
This is an exact original-coordinate equation with no basis choices.

A refined zero-principal-block rank decomposition gives
  rank(W) ≤ rank(C) + rank(QWC).
If rank(W)=4 and rank(C)=2, Hermitianity makes rank(Y)=2.

The next step establishes rank(W)=4 from the exact signed Hamming
eigenquartet and then uses full exchange rank to cancel Yᴴ and Y,
forcing X=0, hence elimination of the 01↔10 Dirac corner.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Refined rank bound for any matrix with a zero diagonal
neutral compression: only the complementary output rank and
the oriented exchange rank contribute. -/
theorem sixMatrix_zeroNeutral_rank_le_complement_plus_exchange
    (W Q : SixMat)
    (hQQ : Q * W * Q = 0) :
    W.rank ≤ (1 - Q : SixMat).rank +
      (Q * W * (1 - Q)).rank := by
  let C : SixMat := 1 - Q
  have hDecomp : W = Q * W * C + C * W := by
    dsimp [C]
    calc
      W = Q * W * Q + Q * W * (1 - Q) +
        (1 - Q) * W := by noncomm_ring
      _ = Q * W * (1 - Q) + (1 - Q) * W := by
        rw [hQQ]
        simp
  have h0 : (C * W).rank ≤ C.rank :=
    Matrix.rank_mul_le_left C W
  have h1 : W.rank ≤ (Q * W * C).rank + (C * W).rank := by
    calc
      W.rank = (Q * W * C + C * W).rank :=
        congrArg Matrix.rank hDecomp
      _ ≤ (Q * W * C).rank + (C * W).rank :=
        sixMatrix_rank_add_le _ _
  change W.rank ≤ C.rank + (Q * W * C).rank
  omega

/-- The neutral compression of a Hermitian cubic signed witness
forces the original active-edge operator X to annihilate the
entire neutral exchange Gram sandwich. -/
theorem sixMatrix_zeroNeutral_cubic_exchange_sandwich_zero
    (W Q : SixMat)
    (hW : W.IsHermitian)
    (hQ : Q * Q = Q)
    (hQH : Q.IsHermitian)
    (hQQ : Q * W * Q = 0)
    (hCubic : W * W * W = W) :
    let C : SixMat := 1 - Q
    let X : SixMat := C * W * C
    let Y : SixMat := C * W * Q
    Y.conjTranspose * X * Y = 0 := by
  dsimp only
  let C : SixMat := 1 - Q
  let X : SixMat := C * W * C
  let Y : SixMat := C * W * Q
  change Y.conjTranspose * X * Y = 0
  have hCC : C * C = C := by
    dsimp [C]
    calc
      (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q := by noncomm_ring
      _ = 1 - Q := by rw [hQ]; abel
  have hQC : Q * C = 0 := by
    dsimp [C]
    calc
      Q * (1 - Q) = Q - Q * Q := by noncomm_ring
      _ = 0 := by rw [hQ]; simp
  have hCQ : C * Q = 0 := by
    dsimp [C]
    calc
      (1 - Q) * Q = Q - Q * Q := by noncomm_ring
      _ = 0 := by rw [hQ]; simp
  have hQW : Q * W = Q * W * C := by
    calc
      Q * W = Q * W * Q + Q * W * C := by
        dsimp [C]
        noncomm_ring
      _ = Q * W * C := by rw [hQQ]; simp
  have hWQ : W * Q = C * W * Q := by
    calc
      W * Q = Q * W * Q + C * W * Q := by
        dsimp [C]
        noncomm_ring
      _ = C * W * Q := by rw [hQQ]; simp
  have hYstar : Y.conjTranspose = Q * W * C := by
    exact sixCornerToNeutralBlock_conjTranspose W Q hW hQH
  have hQcube : Q * (W * W * W) * Q = 0 := by
    rw [hCubic]
    exact hQQ
  have hBlock :
      (Q * W * C) * (C * W * C) * (C * W * Q) =
        Q * (W * W * W) * Q := by
    calc
      (Q * W * C) * (C * W * C) * (C * W * Q) =
          (Q * W * C) * W * (C * W * Q) := by
            calc
              _ = Q * W * (C * C) * W * (C * C) * W * Q := by
                noncomm_ring
              _ = Q * W * C * W * C * W * Q := by rw [hCC]
              _ = (Q * W * C) * W * (C * W * Q) := by noncomm_ring
      _ = (Q * W) * W * (W * Q) := by rw [← hQW, ← hWQ]
      _ = Q * (W * W * W) * Q := by noncomm_ring
  rw [hYstar]
  exact hBlock.trans hQcube

/-- A Hermitian zero-neutral matrix with total rank four and
complementary rank two has a full rank-two active-to-neutral
exchange block. This is purely finite complex matrix algebra. -/
theorem sixMatrix_zeroNeutral_exchange_rank_two
    (W Q : SixMat)
    (hW : W.IsHermitian)
    (hQH : Q.IsHermitian)
    (hQQ : Q * W * Q = 0)
    (hRankW : W.rank = 4)
    (hRankC : (1 - Q : SixMat).rank = 2) :
    ((1 - Q) * W * Q).rank = 2 := by
  let C : SixMat := 1 - Q
  let Y : SixMat := C * W * Q
  change Y.rank = 2
  have hYstar : Y.conjTranspose = Q * W * C :=
    sixCornerToNeutralBlock_conjTranspose W Q hW hQH
  have hUpper : Y.rank ≤ 2 := by
    have hh : Y.rank ≤ C.rank := by
      have t : Y = C * (W * Q) := by dsimp [Y]; noncomm_ring
      rw [t]
      exact Matrix.rank_mul_le_left C (W * Q)
    rw [hRankC] at hh
    exact hh
  have hLower := sixMatrix_zeroNeutral_rank_le_complement_plus_exchange
    W Q hQQ
  change W.rank ≤ C.rank + (Q * W * C).rank at hLower
  rw [hRankW, hRankC] at hLower
  have hRev : (Q * W * C).rank = Y.rank := by
    rw [← hYstar, Matrix.rank_conjTranspose]
  rw [hRev] at hLower
  omega

/-- The original negative signed Hamming witness with singleton
01 and 10 truth fibres satisfies the exact cubic
corner-exchange cancellation, without any saturation assumption. -/
theorem sixLabelled_exactHamming_overneutral_minus_cubic_exchange_sandwich_zero
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
    let X := C * W * C
    let Y := C * W * Q
    Y.conjTranspose * X * Y = 0 := by
  dsimp only
  let W : SixMat := labelledSquareA label D - labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squareMinusNeutral
  have hW : W.IsHermitian :=
    sixLabelled_minusWitness_isHermitian label D hD
  have hQ : Q * Q = Q :=
    sixTruthSectorProjection_idempotent label squareMinusNeutral
  have hQH : Q.IsHermitian :=
    sixTruthSectorProjection_isHermitian label squareMinusNeutral
  have hQQ : Q * W * Q = 0 :=
    sixTruthSectorProjection_W_zero
      label squareMinusNeutral W
      (sixLabelled_minusWitness_neutral_entry_zero label D)
  have hCub := sixLabelled_exactHamming_overneutral_minus_cubic
    label D hD hham hm1 hm2
  change W * W * W = W at hCub
  exact sixMatrix_zeroNeutral_cubic_exchange_sandwich_zero
    W Q hW hQ hQH hQQ hCub

end Neoplatonic.LTR
