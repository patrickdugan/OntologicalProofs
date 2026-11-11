import Neoplatonic.LTR.SixDimensionalSignedOppositeGram
import Neoplatonic.LTR.SixDimensionalSignedCornerRankTwo
import Mathlib.Tactic

/-!
# LTR-MAN-103: exact rank-one defect of a double truth fibre

MAN-96 gives a rank-one projection H=4 BBᴴ for the surviving
oriented opposite Dirac block B in the original six-coordinate
complex Hilbert space. It lies within the orthogonal truth-fibre
projection P of its output atom.

Whenever that fibre has multiplicity two, P-H is itself an
idempotent of trace one, hence has complex rank exactly one.

This identifies the remaining one-dimensional output channel for
the neutral exchange, independent of an arbitrary coordinate
basis in the doubled truth atom.

Two specializations apply directly to exact-Hamming 03-positive
and 12-negative saturated witnesses, with an explicit doubled
output truth fibre.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Subtracting a rank-one subprojection from a rank-two
idempotent yields an idempotent of rank exactly one.
All claims are exact complex matrix identities. -/
theorem sixMatrix_rankTwoProjection_sub_rankOneProjection
    (P H : SixMat)
    (hP : P * P = P)
    (hH : H * H = H)
    (hPH : P * H = H)
    (hHP : H * P = H)
    (hPTrace : P.trace = (2 : ℂ))
    (hHTrace : H.trace = (1 : ℂ)) :
    (P - H) * (P - H) = P - H ∧
      (P - H).rank = 1 := by
  have hproj : (P - H) * (P - H) = P - H := by
    calc
      (P - H) * (P - H) =
          P * P - P * H - H * P + H * H := by noncomm_ring
      _ = P - H := by rw [hP, hH, hPH, hHP]; noncomm_ring
  have htr : (P - H).trace = (1 : ℂ) := by
    rw [Matrix.trace_sub, hPTrace, hHTrace]
    norm_num
  have hRank := sixMatrix_idempotent_trace_eq_rank (P - H) hproj
  rw [htr] at hRank
  exact ⟨hproj, by exact_mod_cast hRank.symm⟩

/-- A two-dimensional truth fibre containing the final Gram
projection of an oriented block B has precisely one remaining
Hilbert coordinate in the projection P-4BBᴴ. -/
theorem sixTruthFibreBlock_doubleFibre_gramDefectRankOne
    (label : Fin 6 → Fin 4) (D : SixMat) (u v : Fin 4)
    (hMult : truthMultiplicity label u = 2)
    (hGram :
      let B := sixTruthFibreBlock label D u v
      let H : SixMat := (4 : ℂ) • (B * B.conjTranspose)
      H * H = H ∧ H.trace = (1 : ℂ)) :
    let B := sixTruthFibreBlock label D u v
    let P := sixTruthFibreProjection label u
    let H : SixMat := (4 : ℂ) • (B * B.conjTranspose)
    (P - H) * (P - H) = P - H ∧
      (P - H).rank = 1 := by
  dsimp only
  let P : SixMat := sixTruthFibreProjection label u
  let R : SixMat := sixTruthFibreProjection label v
  let B : SixMat := sixTruthFibreBlock label D u v
  let H : SixMat := (4 : ℂ) • (B * B.conjTranspose)
  change (P - H) * (P - H) = P - H ∧ (P - H).rank = 1
  change H * H = H ∧ H.trace = (1 : ℂ) at hGram
  obtain ⟨hHid, hHtrace⟩ := hGram
  have hPid : P * P = P := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label
        (fun w : Fin 4 => w = u))
  have hPherm : P.IsHermitian := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_isHermitian label
        (fun w : Fin 4 => w = u))
  have hPB : P * B = B := by
    change P * (P * D * R) = P * D * R
    calc
      P * (P * D * R) = (P * P) * D * R := by noncomm_ring
      _ = P * D * R := by rw [hPid]
  have hBstarP : B.conjTranspose * P = B.conjTranspose := by
    have h := congrArg Matrix.conjTranspose hPB
    rw [Matrix.conjTranspose_mul, hPherm.eq] at h
    exact h
  have hPH : P * H = H := by
    change P * ((4 : ℂ) • (B * B.conjTranspose)) =
      (4 : ℂ) • (B * B.conjTranspose)
    rw [Matrix.mul_smul]
    congr 1
    calc
      P * (B * B.conjTranspose) =
          (P * B) * B.conjTranspose := by noncomm_ring
      _ = B * B.conjTranspose := by rw [hPB]
  have hHP : H * P = H := by
    change ((4 : ℂ) • (B * B.conjTranspose)) * P =
      (4 : ℂ) • (B * B.conjTranspose)
    rw [Matrix.smul_mul]
    congr 1
    calc
      (B * B.conjTranspose) * P =
          B * (B.conjTranspose * P) := by noncomm_ring
      _ = B * B.conjTranspose := by rw [hBstarP]
  have hPtrace : P.trace = (2 : ℂ) := by
    have h :=
      sixTruthSectorProjection_trace_eq_card label
        (fun w : Fin 4 => w = u)
    change P.trace = (truthMultiplicity label u : ℂ) at h
    simpa [hMult] using h
  exact sixMatrix_rankTwoProjection_sub_rankOneProjection
    P H hPid hHid hPH hHP hPtrace hHtrace

/-- At positive 03 saturation with both 00 and 11 doubled,
the 00 final Gram projection leaves a rank-one complementary
truth-fibre channel. -/
theorem sixLabelled_exactHamming_saturated03_double00_gramDefectRankOne
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (hMult : truthMultiplicity label 0 = 2) :
    let B := sixTruthFibreBlock label D 0 3
    let P := sixTruthFibreProjection label 0
    let H : SixMat := (4 : ℂ) • (B * B.conjTranspose)
    (P - H) * (P - H) = P - H ∧ (P - H).rank = 1 := by
  exact sixTruthFibreBlock_doubleFibre_gramDefectRankOne
    label D 0 3 hMult
    (sixLabelled_exactHamming_saturated03_oppositeBlock_quarterGram
      label D hD hham h03 h12)

/-- At negative 12 saturation with the 01 fibre doubled, the
same rank-one Gram defect is certified in the original chart. -/
theorem sixLabelled_exactHamming_saturated12_double01_gramDefectRankOne
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = 0)
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ))
    (hMult : truthMultiplicity label 1 = 2) :
    let B := sixTruthFibreBlock label D 1 2
    let P := sixTruthFibreProjection label 1
    let H : SixMat := (4 : ℂ) • (B * B.conjTranspose)
    (P - H) * (P - H) = P - H ∧ (P - H).rank = 1 := by
  exact sixTruthFibreBlock_doubleFibre_gramDefectRankOne
    label D 1 2 hMult
    (sixLabelled_exactHamming_saturated12_oppositeBlock_quarterGram
      label D hD hham h03 h12)

end Neoplatonic.LTR
