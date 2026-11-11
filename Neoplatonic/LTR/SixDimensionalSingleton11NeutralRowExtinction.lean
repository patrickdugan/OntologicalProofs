import Neoplatonic.LTR.SixDimensionalSingletonNeutralRowExtinction
import Mathlib.Tactic

/-!
# LTR-MAN-110: reverse opposite-channel Gram and singleton 11 extinction

MAN-109 excluded positive saturation when truth fibre 00 is a singleton.
For the reflected (3,1,1,1) pattern the opposite channel terminates
at truth fibre 11. Hermitianity identifies D30 with the adjoint of D03.

We use the existing rank-one, trace-quarter Gram and singleton projector
lemmas on D30, then the right-fibre compression of MAN-104. This proves
the original signed witness neutral-exchange row on truth atom 11
vanishes, without choosing an orthonormal basis.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal ComplexOrder
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The reverse 11-to-00 block has the same exact rank one
and quarter-unit energy as the forward 00-to-11 block. -/
theorem sixLabelled_exactHamming_saturated03_reverseBlock_quarterGram
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    let B := sixTruthFibreBlock label D 3 0
    let H : SixMat := (4 : ℂ) • (B * B.conjTranspose)
    H * H = H ∧ H.trace = (1 : ℂ) := by
  dsimp only
  have hrank : (sixTruthFibreBlock label D 3 0).rank = 1 := by
    have hr := sixLabelled_exactHamming_saturated03_oppositeBlockRankOne
      label D hD hham h03 h12
    have hstar := sixTruthFibreBlock_conjTranspose label D hD 3 0
    rw [← hstar, Matrix.rank_conjTranspose] at hr
    exact hr
  have henergy : sixTruthFibreBlockEnergy label D 3 0 =
      (1 / 4 : ℝ) :=
    (sixTruthFibreBlockEnergy_reverse label D hD 0 3).symm.trans h03
  apply sixMatrix_rankOne_quarterGram_projection
    (sixTruthFibreBlock label D 3 0) hrank
  rw [sixTruthFibreBlock_gram_trace_eq_energy, henergy]
  norm_num

/-- For a singleton 11 endpoint, the reversed saturated
Dirac Gram projector fills the entire truth fibre. -/
theorem sixLabelled_exactHamming_saturated03_singleton11_finalGram
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (hMult : truthMultiplicity label 3 = 1) :
    sixTruthFibreProjection label 3 =
      (4 : ℂ) •
        ((sixTruthFibreBlock label D 3 0) *
          (sixTruthFibreBlock label D 3 0).conjTranspose) := by
  exact sixTruthFibreBlock_singleton_finalGram_eq_fibre
    label D 3 0 hMult
    (sixLabelled_exactHamming_saturated03_reverseBlock_quarterGram
      label D hD hham h03 h12)

/-- A right-oriented scalar Gram has the conjugate coefficient
product, in the original six-dimensional complex matrix. -/
theorem sixMatrix_scalarReverseGram (B : SixMat) (c : ℂ) :
    (c • B).conjTranspose * (c • B) =
      (star c * c) • (B.conjTranspose * B) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul]

/-- The scaled 2i opposite channel has the same unit Gram
factor four in its input truth fibre. -/
theorem sixMatrix_positiveDoubleImagReverseGram (B : SixMat) :
    (((2 : ℂ) * Complex.I) • B).conjTranspose *
        (((2 : ℂ) * Complex.I) • B) =
      (4 : ℂ) • (B.conjTranspose * B) := by
  rw [sixMatrix_scalarReverseGram]
  have hc : ((2 : ℂ) * Complex.I) *
      star ((2 : ℂ) * Complex.I) = 4 := by
    norm_num
    calc
      -(2 * Complex.I * (2 * Complex.I)) =
          -(4 * (Complex.I * Complex.I)) := by ring
      _ = 4 := by rw [Complex.I_mul_I]; ring
  have hc' : star ((2 : ℂ) * Complex.I) *
      ((2 : ℂ) * Complex.I) = 4 := by
    calc
      star ((2 : ℂ) * Complex.I) *
          ((2 : ℂ) * Complex.I) =
        ((2 : ℂ) * Complex.I) *
          star ((2 : ℂ) * Complex.I) := by ring
      _ = 4 := hc
  rw [hc']

/-- At positive 03 saturation, the actual signed neutral exchange
vanishes on truth fibre 11 when its multiplicity is one. -/
theorem sixLabelled_exactHamming_saturated03_singleton11_neutralRow_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (hMult : truthMultiplicity label 3 = 1) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    let R := sixTruthFibreProjection label 3
    let Y := C * W * Q
    R * Y = 0 := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let R : SixMat := sixTruthFibreProjection label 3
  let Y : SixMat := C * W * Q
  let B : SixMat := sixTruthFibreBlock label D 0 3
  let T : SixMat := ((2 : ℂ) * Complex.I) • B
  change R * Y = 0
  have hRH : R.IsHermitian := by
    simpa only [R, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label
        (fun u : Fin 4 => u = 3))
  have hFibre :=
    (sixLabelled_exactHamming_saturated03_fibreNeutralGram
      label D hD hham h03 h12).2
  change R * (Y * Y.conjTranspose) * R =
      R - T.conjTranspose * T at hFibre
  have hFull :=
    sixLabelled_exactHamming_saturated03_singleton11_finalGram
      label D hD hham h03 h12 hMult
  have hreverse : B.conjTranspose =
      sixTruthFibreBlock label D 3 0 :=
    sixTruthFibreBlock_conjTranspose label D hD 0 3
  have hTGram : T.conjTranspose * T =
      (4 : ℂ) • (B.conjTranspose * B) :=
    sixMatrix_positiveDoubleImagReverseGram B
  have hFull' : R = (4 : ℂ) • (B.conjTranspose * B) := by
    change R = (4 : ℂ) •
      ((sixTruthFibreBlock label D 3 0) *
        (sixTruthFibreBlock label D 3 0).conjTranspose) at hFull
    rw [← hreverse, Matrix.conjTranspose_conjTranspose] at hFull
    exact hFull
  have hGram : R * (Y * Y.conjTranspose) * R = 0 := by
    rw [hTGram, ← hFull'] at hFibre
    simpa using hFibre
  exact sixMatrix_hermitianGramCompression_zero_forces_zero
    R Y hRH hGram

end Neoplatonic.LTR
