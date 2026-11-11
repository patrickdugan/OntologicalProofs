import Neoplatonic.LTR.SixDimensionalNeutralRankOnePullbacks
import Neoplatonic.LTR.SixDimensionalSignedFibreNeutralGram
import Mathlib.Tactic

/-!
# LTR-MAN-116: the true saturated 2+2 neutral input has two rank-one channels

MAN-113 proves the original six-dimensional positive signed witness
has exactly two rank-one output defect projections E0 and E3
whose sum equals YYᴴ. MAN-94 proves YᴴY=Q.

Using the MAN-104 fibre-local Gram identities, the two output
defects are supported in orthogonal truth fibres 00 and 11.
They therefore annihilate in both orders.

MAN-115 then transports these two channels back through Y:
  F0 = Yᴴ E0 Y,    F3 = Yᴴ E3 Y.

Both F0 and F3 are rank-one idempotents, they annihilate one another,
and F0+F3=Q. These equalities hold for the *actual* labelled
six-dimensional Dirac matrix, with no chosen singular-vector basis.

The final coordinate-commutator norm bounds and canonical-basis
transport remain further obligations.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- At positive saturation with both opposite truth fibres doubled,
the actual neutral input Q splits into two orthogonal rank-one
pullbacks of the original Dirac Gram defects. -/
theorem sixLabelled_exactHamming_saturated03_oppositeDouble_neutralInputChannels
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (hm0 : truthMultiplicity label 0 = 2)
    (hm3 : truthMultiplicity label 3 = 2) :
    let B := sixTruthFibreBlock label D 0 3
    let P0 := sixTruthFibreProjection label 0
    let P3 := sixTruthFibreProjection label 3
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    let Y := C * W * Q
    let E0 := P0 - (4 : ℂ) • (B * B.conjTranspose)
    let E3 := P3 - (4 : ℂ) • (B.conjTranspose * B)
    let F0 := Y.conjTranspose * E0 * Y
    let F3 := Y.conjTranspose * E3 * Y
    F0 * F0 = F0 ∧ F0.rank = 1 ∧
      F3 * F3 = F3 ∧ F3.rank = 1 ∧
      F0 * F3 = 0 ∧ F3 * F0 = 0 ∧ F0 + F3 = Q := by
  dsimp only
  let B : SixMat := sixTruthFibreBlock label D 0 3
  let P0 : SixMat := sixTruthFibreProjection label 0
  let P3 : SixMat := sixTruthFibreProjection label 3
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let Y : SixMat := C * W * Q
  let T : SixMat := ((2 : ℂ) * Complex.I) • B
  let E0 : SixMat := P0 - (4 : ℂ) • (B * B.conjTranspose)
  let E3 : SixMat := P3 - (4 : ℂ) • (B.conjTranspose * B)
  let F0 : SixMat := Y.conjTranspose * E0 * Y
  let F3 : SixMat := Y.conjTranspose * E3 * Y
  change F0 * F0 = F0 ∧ F0.rank = 1 ∧
    F3 * F3 = F3 ∧ F3.rank = 1 ∧
    F0 * F3 = 0 ∧ F3 * F0 = 0 ∧ F0 + F3 = Q
  obtain ⟨hE0id, hE0rank, hE3id, hE3rank, hYgram⟩ :=
    sixLabelled_exactHamming_saturated03_oppositeDouble_twoRankOneChannels
      label D hD hham h03 h12 hm0 hm3
  change E0 * E0 = E0 at hE0id
  change E0.rank = 1 at hE0rank
  change E3 * E3 = E3 at hE3id
  change E3.rank = 1 at hE3rank
  change Y * Y.conjTranspose = E0 + E3 at hYgram
  have hE0trace : E0.trace = (1 : ℂ) := by
    have h := sixMatrix_idempotent_trace_eq_rank E0 hE0id
    rw [hE0rank] at h
    simpa using h
  have hE3trace : E3.trace = (1 : ℂ) := by
    have h := sixMatrix_idempotent_trace_eq_rank E3 hE3id
    rw [hE3rank] at h
    simpa using h
  have hIso : Y.conjTranspose * Y = Q := by
    have h :=
      (sixLabelled_exactHamming_saturated03_partialIsometry
        label D hD hham h03 h12).2.2
    change Y.conjTranspose * Y = Q at h
    exact h
  have hQid : Q * Q = Q :=
    sixTruthSectorProjection_idempotent label squarePlusNeutral
  obtain ⟨hPR, hRP⟩ := sixOpposite03_fibreProjections_orthogonal label
  have hTGram : T * T.conjTranspose =
      (4 : ℂ) • (B * B.conjTranspose) :=
    sixMatrix_positiveDoubleImagGram B
  have hTrev : T.conjTranspose * T =
      (4 : ℂ) • (B.conjTranspose * B) :=
    sixMatrix_positiveDoubleImagReverseGram B
  obtain ⟨hFibre0, hFibre3⟩ :=
    sixLabelled_exactHamming_saturated03_fibreNeutralGram
      label D hD hham h03 h12
  change P0 * (Y * Y.conjTranspose) * P0 =
      P0 - T * T.conjTranspose at hFibre0
  change P3 * (Y * Y.conjTranspose) * P3 =
      P3 - T.conjTranspose * T at hFibre3
  rw [hTGram] at hFibre0
  rw [hTrev] at hFibre3
  have hE0 : E0 = P0 * (Y * Y.conjTranspose) * P0 :=
    hFibre0.symm
  have hE3 : E3 = P3 * (Y * Y.conjTranspose) * P3 :=
    hFibre3.symm
  have hE03 : E0 * E3 = 0 := by
    rw [hE0, hE3]
    calc
      (P0 * (Y * Y.conjTranspose) * P0) *
          (P3 * (Y * Y.conjTranspose) * P3) =
        P0 * (Y * Y.conjTranspose) * (P0 * P3) *
          (Y * Y.conjTranspose) * P3 := by noncomm_ring
      _ = 0 := by rw [hPR]; simp
  have hE30 : E3 * E0 = 0 := by
    rw [hE3, hE0]
    calc
      (P3 * (Y * Y.conjTranspose) * P3) *
          (P0 * (Y * Y.conjTranspose) * P0) =
        P3 * (Y * Y.conjTranspose) * (P3 * P0) *
          (Y * Y.conjTranspose) * P0 := by noncomm_ring
      _ = 0 := by rw [hRP]; simp
  exact sixMatrix_orthogonalRankOneChannels_pullback
    Y Q E0 E3 hIso hQid hYgram
      hE0id hE3id hE03 hE30 hE0trace hE3trace

end Neoplatonic.LTR
