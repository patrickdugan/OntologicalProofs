import Neoplatonic.LTR.SixDimensionalOppositeFibreProjectionDefect
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic

/-!
# LTR-MAN-105: saturated opposite channel exhausts a singleton truth fibre

The MAN-96 saturated Gram matrix H = 4 B Bᴴ is an idempotent
of trace one. MAN-103 proves it is supported inside the output
truth fibre projector P. If that fibre has multiplicity one,
P and H have the same trace and hence coincide.

A general finite-complex lemma shows an idempotent matrix with
trace zero vanishes, using the genuine linear map and Mathlib's
idempotent endomorphism trace theorem.

Combining these results with MAN-104 will force the neutral
exchange block to vanish on singleton opposite truth atoms.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A six-dimensional complex idempotent of trace zero is the
zero matrix; this uses Mathlib's actual finite-dimensional
endomorphism theorem and introduces no spectral assumption. -/
theorem sixMatrix_idempotent_traceZero_eq_zero
    (M : SixMat)
    (hM : M * M = M)
    (hTrace : M.trace = 0) :
    M = 0 := by
  let e : (Fin 6 → ℂ) →ₗ[ℂ] (Fin 6 → ℂ) := M.toLin'
  have he : IsIdempotentElem e := by
    change e ∘ₗ e = e
    simpa only [e, Matrix.toLin'_mul] using congrArg Matrix.toLin' hM
  have ht : LinearMap.trace ℂ (Fin 6 → ℂ) e = 0 := by
    dsimp only [e]
    rw [Matrix.trace_toLin'_eq]
    exact hTrace
  have hzero : e = 0 :=
    (LinearMap.IsIdempotentElem.trace_eq_zero_iff he).mp ht
  apply Matrix.toLin'.injective
  simpa only [e, map_zero] using hzero

/-- If idempotents H and P have equal trace one and H is
supported inside P on both sides, they coincide exactly. -/
theorem sixMatrix_nestedTraceOneProjectors_equal
    (P H : SixMat)
    (hPid : P * P = P)
    (hHid : H * H = H)
    (hPH : P * H = H)
    (hHP : H * P = H)
    (hPtrace : P.trace = (1 : ℂ))
    (hHtrace : H.trace = (1 : ℂ)) :
    P = H := by
  have hSubId : (P - H) * (P - H) = P - H := by
    calc
      (P - H) * (P - H) =
        P * P - P * H - H * P + H * H := by noncomm_ring
      _ = P - H := by rw [hPid,hPH,hHP,hHid]; noncomm_ring
  have hSubTrace : (P - H).trace = (0 : ℂ) := by
    rw [Matrix.trace_sub, hPtrace, hHtrace]
    ring
  have hSubZero := sixMatrix_idempotent_traceZero_eq_zero
    (P - H) hSubId hSubTrace
  exact sub_eq_zero.mp hSubZero

/-- A saturated rank-one Gram projector exactly fills any
singleton output truth fibre in the original Dirac chart. -/
theorem sixTruthFibreBlock_singleton_finalGram_eq_fibre
    (label : Fin 6 → Fin 4) (D : SixMat)
    (u v : Fin 4)
    (hMult : truthMultiplicity label u = 1)
    (hGram :
      let B := sixTruthFibreBlock label D u v
      let H : SixMat := (4 : ℂ) • (B * B.conjTranspose)
      H * H = H ∧ H.trace = (1 : ℂ)) :
    let B := sixTruthFibreBlock label D u v
    let P := sixTruthFibreProjection label u
    let H : SixMat := (4 : ℂ) • (B * B.conjTranspose)
    P = H := by
  dsimp only
  let P : SixMat := sixTruthFibreProjection label u
  let R : SixMat := sixTruthFibreProjection label v
  let B : SixMat := sixTruthFibreBlock label D u v
  let H : SixMat := (4 : ℂ) • (B * B.conjTranspose)
  change P = H
  change H * H = H ∧ H.trace = (1 : ℂ) at hGram
  obtain ⟨hHid, hHtrace⟩ := hGram
  have hPid : P * P = P := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label
        (fun w : Fin 4 => w = u))
  have hPHerm : P.IsHermitian := by
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
    rw [Matrix.conjTranspose_mul, hPHerm.eq] at h
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
  have hPtrace : P.trace = (1 : ℂ) := by
    have h :=
      sixTruthSectorProjection_trace_eq_card label
        (fun w : Fin 4 => w = u)
    change P.trace = (truthMultiplicity label u : ℂ) at h
    simpa [hMult] using h
  exact sixMatrix_nestedTraceOneProjectors_equal
    P H hPid hHid hPH hHP hPtrace hHtrace

/-- Positive Hamming saturation fills the entire 00 fibre
if it has exactly one Hilbert coordinate. -/
theorem sixLabelled_exactHamming_saturated03_singleton00_finalGram
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0)
    (hMult : truthMultiplicity label 0 = 1) :
    sixTruthFibreProjection label 0 =
      (4 : ℂ) •
        ((sixTruthFibreBlock label D 0 3) *
          (sixTruthFibreBlock label D 0 3).conjTranspose) := by
  exact sixTruthFibreBlock_singleton_finalGram_eq_fibre
    label D 0 3 hMult
    (sixLabelled_exactHamming_saturated03_oppositeBlock_quarterGram
      label D hD hham h03 h12)

/-- Negative Hamming saturation fills a singleton 01 truth fibre
with the surviving oriented 01-to-10 Dirac Gram projector. -/
theorem sixLabelled_exactHamming_saturated12_singleton01_finalGram
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = 0)
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ))
    (hMult : truthMultiplicity label 1 = 1) :
    sixTruthFibreProjection label 1 =
      (4 : ℂ) •
        ((sixTruthFibreBlock label D 1 2) *
          (sixTruthFibreBlock label D 1 2).conjTranspose) := by
  exact sixTruthFibreBlock_singleton_finalGram_eq_fibre
    label D 1 2 hMult
    (sixLabelled_exactHamming_saturated12_oppositeBlock_quarterGram
      label D hD hham h03 h12)

end Neoplatonic.LTR
