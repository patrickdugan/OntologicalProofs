import Neoplatonic.LTR.SixDimensionalSignedNeutralExchangeDefect
import Neoplatonic.LTR.SixDimensionalOppositeFibreProjectionDefect
import Mathlib.Tactic

/-!
# LTR-MAN-104: fibre-local neutral exchange equals opposite Gram defect

MAN-102 established the full original-coordinate identity

  YYᴴ + TTᴴ + TᴴT = P+R,

where P,R project onto the two opposite truth atoms and
T = 2i D03 (or -2i D12) is supported P-to-R.

Multiplying this identity on both sides by P or R yields

  P YYᴴ P = P - TTᴴ,
  R YYᴴ R = R - TᴴT.

These exact identities identify the neutral-exchange channel
within each individual opposite truth fibre without choosing a basis.

MAN-103 establishes that the Gram defect on a doubled fibre
is rank one. MAN-104 prepares the fibre-aligned canonical
basis transport required for the original Hamming no-go theorem.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The two diagonal compressions of the neutral-exchange Gram
are the local defects of the two oriented opposite-block Grams.
This algebraic theorem is independent of truth labels. -/
theorem sixMatrix_twoFibre_neutralGram_compressions
    (P R T S : SixMat)
    (hP2 : P * P = P)
    (hR2 : R * R = R)
    (hPH : P.IsHermitian)
    (hRH : R.IsHermitian)
    (hPR : P * R = 0)
    (hRP : R * P = 0)
    (hPT : P * T = T)
    (hTR : T * R = T)
    (hDefect : S + T * T.conjTranspose +
      T.conjTranspose * T = P + R) :
    P * S * P = P - T * T.conjTranspose ∧
      R * S * R = R - T.conjTranspose * T := by
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
  have hPGram :
      P * (T * T.conjTranspose) * P = T * T.conjTranspose := by
    calc
      P * (T * T.conjTranspose) * P =
        (P * T) * (T.conjTranspose * P) := by noncomm_ring
      _ = T * T.conjTranspose := by rw [hPT, hZP]
  have hPCross :
      P * (T.conjTranspose * T) * P = 0 := by
    calc
      P * (T.conjTranspose * T) * P =
        (P * T.conjTranspose) * (T * P) := by noncomm_ring
      _ = 0 := by rw [hPZ, hTP]; simp
  have hRGram :
      R * (T.conjTranspose * T) * R = T.conjTranspose * T := by
    calc
      R * (T.conjTranspose * T) * R =
        (R * T.conjTranspose) * (T * R) := by noncomm_ring
      _ = T.conjTranspose * T := by rw [hRZ, hTR]
  have hRCross :
      R * (T * T.conjTranspose) * R = 0 := by
    calc
      R * (T * T.conjTranspose) * R =
        (R * T) * (T.conjTranspose * R) := by noncomm_ring
      _ = 0 := by rw [hRT, hZR]; simp
  have hPRHS : P * (P + R) * P = P := by
    calc
      P * (P + R) * P = P * P * P + P * R * P := by noncomm_ring
      _ = P := by rw [hP2, hPR, hP2]; simp
  have hRRHS : R * (P + R) * R = R := by
    calc
      R * (P + R) * R = R * P * R + R * R * R := by noncomm_ring
      _ = R := by rw [hRP, hR2, hR2]; simp
  have hPsum : P * S * P + T * T.conjTranspose = P := by
    calc
      P * S * P + T * T.conjTranspose =
        P * (S + T * T.conjTranspose + T.conjTranspose * T) * P := by
          rw [show P * (S + T * T.conjTranspose +
            T.conjTranspose * T) * P =
            P * S * P + P * (T * T.conjTranspose) * P +
              P * (T.conjTranspose * T) * P from by noncomm_ring]
          rw [hPGram, hPCross]; simp
      _ = P * (P + R) * P := by rw [hDefect]
      _ = P := hPRHS
  have hRsum : R * S * R + T.conjTranspose * T = R := by
    calc
      R * S * R + T.conjTranspose * T =
        R * (S + T * T.conjTranspose + T.conjTranspose * T) * R := by
          rw [show R * (S + T * T.conjTranspose +
            T.conjTranspose * T) * R =
            R * S * R + R * (T * T.conjTranspose) * R +
              R * (T.conjTranspose * T) * R from by noncomm_ring]
          rw [hRCross, hRGram]; simp
      _ = R * (P + R) * R := by rw [hDefect]
      _ = R := hRRHS
  constructor
  · calc
      P * S * P =
          (P * S * P + T * T.conjTranspose) -
            T * T.conjTranspose := by abel
      _ = P - T * T.conjTranspose := by rw [hPsum]
  · calc
      R * S * R =
          (R * S * R + T.conjTranspose * T) -
            T.conjTranspose * T := by abel
      _ = R - T.conjTranspose * T := by rw [hRsum]

/-- The exact positive signed witness neutral exchange in each
opposite truth atom equals the corresponding oriented Gram defect
of the original six-dimensional Dirac coupling. -/
theorem sixLabelled_exactHamming_saturated03_fibreNeutralGram
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
    let T := ((2 : ℂ) * Complex.I) • sixTruthFibreBlock label D 0 3
    P * (Y * Y.conjTranspose) * P = P - T * T.conjTranspose ∧
      R * (Y * Y.conjTranspose) * R = R - T.conjTranspose * T := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let P : SixMat := sixTruthFibreProjection label 0
  let R : SixMat := sixTruthFibreProjection label 3
  let Y : SixMat := C * W * Q
  let T : SixMat := ((2 : ℂ) * Complex.I) •
    sixTruthFibreBlock label D 0 3
  change P * (Y * Y.conjTranspose) * P =
      P - T * T.conjTranspose ∧
    R * (Y * Y.conjTranspose) * R =
      R - T.conjTranspose * T
  have hP2 : P * P = P := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label (fun u : Fin 4 => u = 0))
  have hR2 : R * R = R := by
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
      _ = P * D * R := by rw [hP2]
  have hTR : T * R = T := by
    change (((2 : ℂ) * Complex.I) • (P * D * R)) * R =
      ((2 : ℂ) * Complex.I) • (P * D * R)
    rw [Matrix.smul_mul]
    congr 1
    calc
      (P * D * R) * R = P * D * (R * R) := by noncomm_ring
      _ = P * D * R := by rw [hR2]
  have hDef := sixLabelled_exactHamming_saturated03_neutralExchange_defect
    label D hD hham h03 h12
  change Y * Y.conjTranspose +
    T * T.conjTranspose + T.conjTranspose * T = C at hDef
  have hC : C = P + R := sixPlus_complement_eq_oppositeFibreProjections label
  rw [hC] at hDef
  exact sixMatrix_twoFibre_neutralGram_compressions
    P R T (Y * Y.conjTranspose)
    hP2 hR2 hPH hRH hPR hRP hPT hTR hDef

/-- Negative 01/10 saturation gives the same fibre-local defect
for the original -2i-scaled Dirac opposite block. -/
theorem sixLabelled_exactHamming_saturated12_fibreNeutralGram
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
    let T := ((-2 : ℂ) * Complex.I) • sixTruthFibreBlock label D 1 2
    P * (Y * Y.conjTranspose) * P = P - T * T.conjTranspose ∧
      R * (Y * Y.conjTranspose) * R = R - T.conjTranspose * T := by
  dsimp only
  let W : SixMat := labelledSquareA label D - labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squareMinusNeutral
  let C : SixMat := 1 - Q
  let P : SixMat := sixTruthFibreProjection label 1
  let R : SixMat := sixTruthFibreProjection label 2
  let Y : SixMat := C * W * Q
  let T : SixMat := ((-2 : ℂ) * Complex.I) •
    sixTruthFibreBlock label D 1 2
  change P * (Y * Y.conjTranspose) * P =
      P - T * T.conjTranspose ∧
    R * (Y * Y.conjTranspose) * R =
      R - T.conjTranspose * T
  have hP2 : P * P = P := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label (fun u : Fin 4 => u = 1))
  have hR2 : R * R = R := by
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
      _ = P * D * R := by rw [hP2]
  have hTR : T * R = T := by
    change (((-2 : ℂ) * Complex.I) • (P * D * R)) * R =
      ((-2 : ℂ) * Complex.I) • (P * D * R)
    rw [Matrix.smul_mul]
    congr 1
    calc
      (P * D * R) * R = P * D * (R * R) := by noncomm_ring
      _ = P * D * R := by rw [hR2]
  have hDef := sixLabelled_exactHamming_saturated12_neutralExchange_defect
    label D hD hham h03 h12
  change Y * Y.conjTranspose +
    T * T.conjTranspose + T.conjTranspose * T = C at hDef
  have hC : C = P + R := sixMinus_complement_eq_oppositeFibreProjections label
  rw [hC] at hDef
  exact sixMatrix_twoFibre_neutralGram_compressions
    P R T (Y * Y.conjTranspose)
    hP2 hR2 hPH hRH hPR hRP hPT hTR hDef

end Neoplatonic.LTR
