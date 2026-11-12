import Neoplatonic.LTR.SixDimensionalNearHalfNeutralSingletons
import Neoplatonic.LTR.SixDimensionalSaturated03TransitionTrace
import Neoplatonic.LTR.SixDimensionalSignedOppositeGramCornerBridge
import Neoplatonic.LTR.SixDimensionalOppositeCornerEntryBound
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-164: nonsaturated fibre-local Gram and transition trace budgets

Quantitative successors of MAN-104 and MAN-117, in the original
six-dimensional complex Hilbert matrix coordinates.

For the plus witness W, Q is the 01/10 neutral projection, C=I-Q,
X=CWC, Y=CWQ, Δ=I-W², and T=2i D03.

MAN-140 gives X²+YYᴴ=C-CΔC. MAN-100 gives
X²=TTᴴ+TᴴT. Compressing to the two 00/11 output fibres yields

 P0 YYᴴ P0 = P0-TTᴴ-P0ΔP0,
 P3 YYᴴ P3 = P3-TᴴT-P3ΔP3.

The projection-defect trace is bounded by the fibre multiplicity
times ||Δ||. The neutral column identity, from YᴴY=Q-QΔQ, reads
 Tr(YN Yᴴ)+Tr(NΔN)=Tr(N).

These are exact nonsaturated identities. Later declarations
specialize them to the 2+2 opposite-fibre case with ||Δ||≤2ε.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- MAN-104 with a genuine nonsaturated spectral defect:
both opposite output-fibre Gram equations retain the exact
local defect compression. -/
theorem sixMatrix_twoFibre_neutralGram_perturbedCompressions
    (P R T S C Δ : SixMat)
    (hP2 : P * P = P) (hR2 : R * R = R)
    (hPH : P.IsHermitian) (hRH : R.IsHermitian)
    (hPR : P * R = 0) (hRP : R * P = 0)
    (hPT : P * T = T) (hTR : T * R = T)
    (hC : C = P + R)
    (hGram : S + T * T.conjTranspose +
      T.conjTranspose * T = C - C * Δ * C) :
    P * S * P = P - T * T.conjTranspose - P * Δ * P ∧
      R * S * R = R - T.conjTranspose * T - R * Δ * R := by
  let U : SixMat := S + C * Δ * C
  have hSum : U + T * T.conjTranspose +
      T.conjTranspose * T = P + R := by
    dsimp [U]
    calc
      S + C * Δ * C + T * T.conjTranspose +
          T.conjTranspose * T =
          (S + T * T.conjTranspose + T.conjTranspose * T) +
            C * Δ * C := by abel
      _ = C := by rw [hGram]; abel
      _ = P + R := hC
  have hBase := sixMatrix_twoFibre_neutralGram_compressions
    P R T U hP2 hR2 hPH hRH hPR hRP hPT hTR hSum
  have hPC : P * C = P := by
    rw [hC]
    calc
      P * (P + R) = P * P + P * R := by noncomm_ring
      _ = P := by rw [hP2, hPR]; simp
  have hCP : C * P = P := by
    rw [hC]
    calc
      (P + R) * P = P * P + R * P := by noncomm_ring
      _ = P := by rw [hP2, hRP]; simp
  have hRC : R * C = R := by
    rw [hC]
    calc
      R * (P + R) = R * P + R * R := by noncomm_ring
      _ = R := by rw [hRP, hR2]; simp
  have hCR : C * R = R := by
    rw [hC]
    calc
      (P + R) * R = P * R + R * R := by noncomm_ring
      _ = R := by rw [hPR, hR2]; simp
  have hPΔ : P * (C * Δ * C) * P = P * Δ * P := by
    calc
      P * (C * Δ * C) * P = (P * C) * Δ * (C * P) := by
        noncomm_ring
      _ = P * Δ * P := by rw [hPC, hCP]
  have hRΔ : R * (C * Δ * C) * R = R * Δ * R := by
    calc
      R * (C * Δ * C) * R = (R * C) * Δ * (C * R) := by
        noncomm_ring
      _ = R * Δ * R := by rw [hRC, hCR]
  constructor
  · calc
      P * S * P = P * U * P - P * (C * Δ * C) * P := by
        dsimp [U]
        noncomm_ring
      _ = P - T * T.conjTranspose - P * Δ * P := by
        rw [hBase.1, hPΔ]
  · calc
      R * S * R = R * U * R - R * (C * Δ * C) * R := by
        dsimp [U]
        noncomm_ring
      _ = R - T.conjTranspose * T - R * Δ * R := by
        rw [hBase.2, hRΔ]

/-- The Euclidean operator norm bounds the trace of an arbitrary
matrix compressed to an original truth-atom fibre: its coefficient
is precisely that fibre's multiplicity. -/
theorem sixTruthFibreProjection_defectTrace_norm_le
    (label : Fin 6 → Fin 4) (M : SixMat) (u : Fin 4) :
    ‖(sixTruthFibreProjection label u * M *
       sixTruthFibreProjection label u).trace‖ ≤
      (truthMultiplicity label u : ℝ) * ‖M‖ := by
  let P : SixMat := sixTruthFibreProjection label u
  have hPid : P * P = P := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection]
      using sixTruthSectorProjection_idempotent
        label (fun t : Fin 4 => t = u)
  have hTrace : (P * M * P).trace =
      ∑ i : Fin 6, if label i = u then M i i else 0 := by
    rw [sixMatrix_trace_doubleCompression_eq_leftCompression P M hPid]
    simp [P, sixTruthFibreProjection, Matrix.trace, Matrix.diag,
      Matrix.diagonal_mul]
  have hentry (i : Fin 6) : ‖M i i‖ ≤ ‖M‖ := by
    rw [Matrix.cstar_norm_def]
    change ‖M i i‖ ≤ ‖M.toEuclideanLin.toContinuousLinearMap‖
    exact sixMatrix_entryNorm_le_operatorNorm M i i
  rw [hTrace]
  calc
    ‖∑ i : Fin 6, if label i = u then M i i else 0‖ ≤
      ∑ i : Fin 6, ‖if label i = u then M i i else 0‖ :=
        norm_sum_le _ _
    _ ≤ ∑ i : Fin 6, if label i = u then ‖M‖ else 0 := by
      apply Finset.sum_le_sum
      intro i hi
      by_cases h : label i = u <;> simp [h, hentry i]
    _ = (truthMultiplicity label u : ℝ) * ‖M‖ := by
      simp [truthMultiplicity, Finset.sum_ite, Finset.sum_const,
        nsmul_eq_mul]
      ring

/-- The exact column trace identity of a neutral exchange with
nonzero signed spectral defect. This includes any singleton
neutral input fibre N, once its Q-support is certified. -/
theorem sixMatrix_neutralColumnTrace_defect
    (Y Q N Δ : SixMat)
    (hNid : N * N = N)
    (hQN : Q * N = N) (hNQ : N * Q = N)
    (hGram : Y.conjTranspose * Y = Q - Q * Δ * Q) :
    (Y * N * Y.conjTranspose).trace + (N * Δ * N).trace =
      N.trace := by
  have hTrace : (Q * Δ * N).trace = (N * Δ * N).trace := by
    calc
      (Q * Δ * N).trace = (N * (Q * Δ)).trace := by
        simpa only [Matrix.mul_assoc] using
          (Matrix.trace_mul_comm (Q * Δ) N)
      _ = (N * Δ).trace := by
        rw [← Matrix.mul_assoc, hNQ]
      _ = (N * Δ * N).trace :=
        (sixMatrix_trace_doubleCompression_eq_leftCompression
          N Δ hNid).symm
  have hFirst : (Y * N * Y.conjTranspose).trace =
      N.trace - (N * Δ * N).trace := by
    calc
      (Y * N * Y.conjTranspose).trace =
          (Y.conjTranspose * (Y * N)).trace := by
            simpa only [Matrix.mul_assoc] using
              (Matrix.trace_mul_comm (Y * N) Y.conjTranspose)
      _ = ((Y.conjTranspose * Y) * N).trace := by
        rw [Matrix.mul_assoc]
      _ = ((Q - Q * Δ * Q) * N).trace := by rw [hGram]
      _ = (N - Q * Δ * N).trace := by
        congr 1
        rw [Matrix.sub_mul, hQN]
        congr 1
        noncomm_ring
      _ = N.trace - (N * Δ * N).trace := by
        rw [Matrix.trace_sub, hTrace]
  linear_combination hFirst

end Neoplatonic.LTR
