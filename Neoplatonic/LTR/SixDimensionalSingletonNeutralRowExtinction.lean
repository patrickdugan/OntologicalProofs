import Neoplatonic.LTR.SixDimensionalSingletonOppositeExhaustion
import Neoplatonic.LTR.SixDimensionalSignedFibreNeutralGram
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic

/-!
# LTR-MAN-106: singleton opposite truth atom has zero neutral-exchange row

A saturated opposite Dirac Gram projector completely fills a
singleton opposite truth fibre (MAN-105). The MAN-104 exact
compression identity then gives

  P Y Yᴴ P = 0.

For a Hermitian truth-fibre projector P, this is precisely
(PY)(PY)ᴴ=0. The faithful complex matrix self-Gram theorem
therefore implies PY=0.

The result is the crucial support extinction used in the
triple-corner separating-function obstruction. It is proved
in the true six-coordinate Dirac chart.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal ComplexOrder

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A Hermitian compression of the Gram of Y vanishes precisely
when its corresponding matrix row block P*Y vanishes. -/
theorem sixMatrix_hermitianGramCompression_zero_forces_zero
    (P Y : SixMat)
    (hPH : P.IsHermitian)
    (hGram : P * (Y * Y.conjTranspose) * P = 0) :
    P * Y = 0 := by
  have hSelf : (P * Y) * (P * Y).conjTranspose = 0 := by
    rw [Matrix.conjTranspose_mul, hPH.eq]
    calc
      (P * Y) * (Y.conjTranspose * P) =
        P * (Y * Y.conjTranspose) * P := by noncomm_ring
      _ = 0 := hGram
  exact Matrix.self_mul_conjTranspose_eq_zero.mp hSelf

/-- The oriented Gram of a scalar multiple of any complex
matrix has the exact squared scalar coefficient. -/
theorem sixMatrix_scalarGram (B : SixMat) (c : ℂ) :
    (c • B) * (c • B).conjTranspose =
      (c * star c) • (B * B.conjTranspose) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]

/-- The exact positive 2i Hamming coefficient has squared
magnitude four in the complex matrix Gram. -/
theorem sixMatrix_positiveDoubleImagGram (B : SixMat) :
    (((2 : ℂ) * Complex.I) • B) *
        (((2 : ℂ) * Complex.I) • B).conjTranspose =
      (4 : ℂ) • (B * B.conjTranspose) := by
  rw [sixMatrix_scalarGram]
  have hc : ((2 : ℂ) * Complex.I) *
      star ((2 : ℂ) * Complex.I) = 4 := by
    norm_num
    calc
      -(2 * Complex.I * (2 * Complex.I)) =
          -(4 * (Complex.I * Complex.I)) := by ring
      _ = 4 := by rw [Complex.I_mul_I]; ring
  rw [hc]

/-- The negative signed witness coefficient -2i has exactly
the same complex squared Gram factor. -/
theorem sixMatrix_negativeDoubleImagGram (B : SixMat) :
    (((-2 : ℂ) * Complex.I) • B) *
        (((-2 : ℂ) * Complex.I) • B).conjTranspose =
      (4 : ℂ) • (B * B.conjTranspose) := by
  rw [sixMatrix_scalarGram]
  have hc : ((-2 : ℂ) * Complex.I) *
      star ((-2 : ℂ) * Complex.I) = 4 := by
    norm_num
    calc
      -(2 * Complex.I * (2 * Complex.I)) =
          -(4 * (Complex.I * Complex.I)) := by ring
      _ = 4 := by rw [Complex.I_mul_I]; ring
  rw [hc]

/-- At positive 00/11 saturation, a singleton 00 truth atom
has no neutral-exchange component at all in the original
six-dimensional Dirac witness. -/
theorem sixLabelled_exactHamming_saturated03_singleton00_neutralRow_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (hMult : truthMultiplicity label 0 = 1) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    let P := sixTruthFibreProjection label 0
    let Y := C * W * Q
    P * Y = 0 := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let P : SixMat := sixTruthFibreProjection label 0
  let Y : SixMat := C * W * Q
  let B : SixMat := sixTruthFibreBlock label D 0 3
  let T : SixMat := ((2 : ℂ) * Complex.I) • B
  change P * Y = 0
  have hPH : P.IsHermitian := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label
        (fun u : Fin 4 => u = 0))
  have hFibre :=
    (sixLabelled_exactHamming_saturated03_fibreNeutralGram
      label D hD hham h03 h12).1
  change P * (Y * Y.conjTranspose) * P =
      P - T * T.conjTranspose at hFibre
  have hFull :=
    sixLabelled_exactHamming_saturated03_singleton00_finalGram
      label D hD hham h03 h12 hMult
  change P = (4 : ℂ) • (B * B.conjTranspose) at hFull
  have hTGram : T * T.conjTranspose =
      (4 : ℂ) • (B * B.conjTranspose) :=
    sixMatrix_positiveDoubleImagGram B
  have hGram : P * (Y * Y.conjTranspose) * P = 0 := by
    rw [hTGram, ← hFull] at hFibre
    simpa using hFibre
  exact sixMatrix_hermitianGramCompression_zero_forces_zero
    P Y hPH hGram

/-- At negative 01/10 saturation, a singleton 01 truth atom
has zero neutral-exchange row in the actual labelled witness. -/
theorem sixLabelled_exactHamming_saturated12_singleton01_neutralRow_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = 0)
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ))
    (hMult : truthMultiplicity label 1 = 1) :
    let W := labelledSquareA label D - labelledSquareB label D
    let Q := sixTruthSectorProjection label squareMinusNeutral
    let C := (1 - Q : SixMat)
    let P := sixTruthFibreProjection label 1
    let Y := C * W * Q
    P * Y = 0 := by
  dsimp only
  let W : SixMat := labelledSquareA label D - labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squareMinusNeutral
  let C : SixMat := 1 - Q
  let P : SixMat := sixTruthFibreProjection label 1
  let Y : SixMat := C * W * Q
  let B : SixMat := sixTruthFibreBlock label D 1 2
  let T : SixMat := ((-2 : ℂ) * Complex.I) • B
  change P * Y = 0
  have hPH : P.IsHermitian := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label
        (fun u : Fin 4 => u = 1))
  have hFibre :=
    (sixLabelled_exactHamming_saturated12_fibreNeutralGram
      label D hD hham h03 h12).1
  change P * (Y * Y.conjTranspose) * P =
      P - T * T.conjTranspose at hFibre
  have hFull :=
    sixLabelled_exactHamming_saturated12_singleton01_finalGram
      label D hD hham h03 h12 hMult
  change P = (4 : ℂ) • (B * B.conjTranspose) at hFull
  have hTGram : T * T.conjTranspose =
      (4 : ℂ) • (B * B.conjTranspose) :=
    sixMatrix_negativeDoubleImagGram B
  have hGram : P * (Y * Y.conjTranspose) * P = 0 := by
    rw [hTGram, ← hFull] at hFibre
    simpa using hFibre
  exact sixMatrix_hermitianGramCompression_zero_forces_zero
    P Y hPH hGram

end Neoplatonic.LTR
