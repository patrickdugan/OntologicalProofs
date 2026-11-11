import Neoplatonic.LTR.SixDimensionalSignedFibreNeutralGram
import Mathlib.Tactic

/-!
# LTR-MAN-114: cross-fibre orthogonality of saturated neutral exchange

MAN-102 and MAN-104 identify the neutral exchange Gram S=YYᴴ with
the complement of the two Gram terms TTᴴ and TᴴT inside a sum
of orthogonal truth-fibre projectors P+R.

This module proves that S has zero cross-fibre matrix blocks:

  P S R = 0,  R S P = 0.

The theorem applies in the original six-dimensional labelled Dirac
representation, for both positive and negative pure saturation signs.
It supplies the abstract row-orthogonality condition of the
U(2) normal form without choosing fibre bases.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- In an orthogonal two-fibre corner, neutral exchange Gram has
no off-diagonal fibre-to-fibre components. -/
theorem sixMatrix_twoFibre_neutralGram_cross_zero
    (P R T S : SixMat)
    (hPP : P * P = P)
    (hRR : R * R = R)
    (hPH : P.IsHermitian)
    (hRH : R.IsHermitian)
    (hPR : P * R = 0)
    (hRP : R * P = 0)
    (hPT : P * T = T)
    (hTR : T * R = T)
    (hDefect : S + T * T.conjTranspose +
      T.conjTranspose * T = P + R) :
    P * S * R = 0 ∧ R * S * P = 0 := by
  have hZP : T.conjTranspose * P = T.conjTranspose := by
    have h := congrArg Matrix.conjTranspose hPT
    simpa only [Matrix.conjTranspose_mul, hPH.eq] using h
  have hRZ : R * T.conjTranspose = T.conjTranspose := by
    have h := congrArg Matrix.conjTranspose hTR
    simpa only [Matrix.conjTranspose_mul, hRH.eq] using h
  have hPZ : P * T.conjTranspose = 0 := by
    calc
      P * T.conjTranspose = P * (R * T.conjTranspose) := by rw [hRZ]
      _ = (P * R) * T.conjTranspose := by noncomm_ring
      _ = 0 := by rw [hPR]; simp
  have hZR : T.conjTranspose * R = 0 := by
    calc
      T.conjTranspose * R = (T.conjTranspose * P) * R := by rw [hZP]
      _ = T.conjTranspose * (P * R) := by noncomm_ring
      _ = 0 := by rw [hPR]; simp
  have hTP : T * P = 0 := by
    calc
      T * P = (T * R) * P := by rw [hTR]
      _ = T * (R * P) := by noncomm_ring
      _ = 0 := by rw [hRP]; simp
  have hRT : R * T = 0 := by
    calc
      R * T = R * (P * T) := by rw [hPT]
      _ = (R * P) * T := by noncomm_ring
      _ = 0 := by rw [hRP]; simp
  have hPGram : P * (T * T.conjTranspose) * R = 0 := by
    calc
      P * (T * T.conjTranspose) * R =
        (P * T) * (T.conjTranspose * R) := by noncomm_ring
      _ = 0 := by rw [hZR]; simp
  have hPCross : P * (T.conjTranspose * T) * R = 0 := by
    calc
      P * (T.conjTranspose * T) * R =
        (P * T.conjTranspose) * (T * R) := by noncomm_ring
      _ = 0 := by rw [hPZ]; simp
  have hRGram : R * (T * T.conjTranspose) * P = 0 := by
    calc
      R * (T * T.conjTranspose) * P =
        (R * T) * (T.conjTranspose * P) := by noncomm_ring
      _ = 0 := by rw [hRT]; simp
  have hRCross : R * (T.conjTranspose * T) * P = 0 := by
    calc
      R * (T.conjTranspose * T) * P =
        (R * T.conjTranspose) * (T * P) := by noncomm_ring
      _ = 0 := by rw [hTP]; simp
  have hPcorner : P * (P + R) * R = 0 := by
    calc
      P * (P + R) * R = (P * P) * R + P * (R * R) := by
        noncomm_ring
      _ = 0 := by rw [hPP, hRR, hPR]; simp
  have hRcorner : R * (P + R) * P = 0 := by
    calc
      R * (P + R) * P = (R * P) * P + R * (R * P) := by
        noncomm_ring
      _ = 0 := by rw [hRP]; simp
  have hPsum :
      P * S * R + P * (T * T.conjTranspose) * R +
        P * (T.conjTranspose * T) * R = P * (P + R) * R := by
    calc
      _ = P * (S + T * T.conjTranspose +
          T.conjTranspose * T) * R := by noncomm_ring
      _ = P * (P + R) * R := by rw [hDefect]
  have hRsum :
      R * S * P + R * (T * T.conjTranspose) * P +
        R * (T.conjTranspose * T) * P = R * (P + R) * P := by
    calc
      _ = R * (S + T * T.conjTranspose +
          T.conjTranspose * T) * P := by noncomm_ring
      _ = R * (P + R) * P := by rw [hDefect]
  constructor
  · rw [hPGram, hPCross, hPcorner] at hPsum
    simpa using hPsum
  · rw [hRGram, hRCross, hRcorner] at hRsum
    simpa using hRsum

/-- The true 00 and 11 neutral-exchange Gram cross-blocks vanish
under positive 03 saturation, independently of fibre multiplicity. -/
theorem sixLabelled_exactHamming_saturated03_neutralCrossGram_zero
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
    let P := sixTruthFibreProjection label 0
    let R := sixTruthFibreProjection label 3
    let Y := C * W * Q
    P * (Y * Y.conjTranspose) * R = 0 ∧
      R * (Y * Y.conjTranspose) * P = 0 := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let P : SixMat := sixTruthFibreProjection label 0
  let R : SixMat := sixTruthFibreProjection label 3
  let Y : SixMat := C * W * Q
  let T : SixMat := ((2 : ℂ) * Complex.I) •
    sixTruthFibreBlock label D 0 3
  change P * (Y * Y.conjTranspose) * R = 0 ∧
    R * (Y * Y.conjTranspose) * P = 0
  have hPP : P * P = P := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label (fun u : Fin 4 => u = 0))
  have hRR : R * R = R := by
    simpa only [R, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label (fun u : Fin 4 => u = 3))
  have hPH : P.IsHermitian := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label (fun u : Fin 4 => u = 0))
  have hRH : R.IsHermitian := by
    simpa only [R, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label (fun u : Fin 4 => u = 3))
  obtain ⟨hPR, hRP⟩ := sixOpposite03_fibreProjections_orthogonal label
  have hPT : P * T = T := by
    change P * (((2 : ℂ) * Complex.I) • (P * D * R)) =
      ((2 : ℂ) * Complex.I) • (P * D * R)
    rw [Matrix.mul_smul]
    congr 1
    calc
      P * (P * D * R) = (P * P) * D * R := by noncomm_ring
      _ = P * D * R := by rw [hPP]
  have hTR : T * R = T := by
    change (((2 : ℂ) * Complex.I) • (P * D * R)) * R =
      ((2 : ℂ) * Complex.I) • (P * D * R)
    rw [Matrix.smul_mul]
    congr 1
    calc
      (P * D * R) * R = P * D * (R * R) := by noncomm_ring
      _ = P * D * R := by rw [hRR]
  have hDef := sixLabelled_exactHamming_saturated03_neutralExchange_defect
    label D hD hham h03 h12
  change Y * Y.conjTranspose + T * T.conjTranspose +
    T.conjTranspose * T = C at hDef
  have hC : C = P + R :=
    sixPlus_complement_eq_oppositeFibreProjections label
  rw [hC] at hDef
  exact sixMatrix_twoFibre_neutralGram_cross_zero
    P R T (Y * Y.conjTranspose)
    hPP hRR hPH hRH hPR hRP hPT hTR hDef

/-- Same cross-Gram orthogonality for the 01 and 10 truth fibres
at pure negative 12 saturation. -/
theorem sixLabelled_exactHamming_saturated12_neutralCrossGram_zero
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
    let P := sixTruthFibreProjection label 1
    let R := sixTruthFibreProjection label 2
    let Y := C * W * Q
    P * (Y * Y.conjTranspose) * R = 0 ∧
      R * (Y * Y.conjTranspose) * P = 0 := by
  dsimp only
  let W : SixMat := labelledSquareA label D - labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squareMinusNeutral
  let C : SixMat := 1 - Q
  let P : SixMat := sixTruthFibreProjection label 1
  let R : SixMat := sixTruthFibreProjection label 2
  let Y : SixMat := C * W * Q
  let T : SixMat := ((-2 : ℂ) * Complex.I) •
    sixTruthFibreBlock label D 1 2
  change P * (Y * Y.conjTranspose) * R = 0 ∧
    R * (Y * Y.conjTranspose) * P = 0
  have hPP : P * P = P := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label (fun u : Fin 4 => u = 1))
  have hRR : R * R = R := by
    simpa only [R, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label (fun u : Fin 4 => u = 2))
  have hPH : P.IsHermitian := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label (fun u : Fin 4 => u = 1))
  have hRH : R.IsHermitian := by
    simpa only [R, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label (fun u : Fin 4 => u = 2))
  obtain ⟨hPR, hRP⟩ := sixOpposite12_fibreProjections_orthogonal label
  have hPT : P * T = T := by
    change P * (((-2 : ℂ) * Complex.I) • (P * D * R)) =
      ((-2 : ℂ) * Complex.I) • (P * D * R)
    rw [Matrix.mul_smul]
    congr 1
    calc
      P * (P * D * R) = (P * P) * D * R := by noncomm_ring
      _ = P * D * R := by rw [hPP]
  have hTR : T * R = T := by
    change (((-2 : ℂ) * Complex.I) • (P * D * R)) * R =
      ((-2 : ℂ) * Complex.I) • (P * D * R)
    rw [Matrix.smul_mul]
    congr 1
    calc
      (P * D * R) * R = P * D * (R * R) := by noncomm_ring
      _ = P * D * R := by rw [hRR]
  have hDef := sixLabelled_exactHamming_saturated12_neutralExchange_defect
    label D hD hham h03 h12
  change Y * Y.conjTranspose + T * T.conjTranspose +
    T.conjTranspose * T = C at hDef
  have hC : C = P + R :=
    sixMinus_complement_eq_oppositeFibreProjections label
  rw [hC] at hDef
  exact sixMatrix_twoFibre_neutralGram_cross_zero
    P R T (Y * Y.conjTranspose)
    hPP hRR hPH hRH hPR hRP hPT hTR hDef

end Neoplatonic.LTR
