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
        calc
          (Q - Q * Δ * Q) * N =
              Q * N - Q * Δ * (Q * N) := by noncomm_ring
          _ = N - Q * Δ * N := by rw [hQN]
      _ = N.trace - (N * Δ * N).trace := by
        rw [Matrix.trace_sub, hTrace]
  linear_combination hFirst


/-- The nonsaturated MAN-140/100 square equations give exact
local output-fibre Gram formulas for the original positive
Dirac witness, in the same fixed six-dimensional coordinates. -/
theorem sixLabelled_plusWitness_nonsaturated_fibreNeutralGram
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    let Y := C * W * Q
    let Δ := (1 : SixMat) - W * W
    let P0 := sixTruthFibreProjection label 0
    let P3 := sixTruthFibreProjection label 3
    let T := ((2 : ℂ) * Complex.I) • sixTruthFibreBlock label D 0 3
    P0 * (Y * Y.conjTranspose) * P0 =
      P0 - T * T.conjTranspose - P0 * Δ * P0 ∧
    P3 * (Y * Y.conjTranspose) * P3 =
      P3 - T.conjTranspose * T - P3 * Δ * P3 := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let X : SixMat := C * W * C
  let Y : SixMat := C * W * Q
  let Δ : SixMat := 1 - W * W
  let P0 : SixMat := sixTruthFibreProjection label 0
  let P3 : SixMat := sixTruthFibreProjection label 3
  let T : SixMat := ((2 : ℂ) * Complex.I) •
    sixTruthFibreBlock label D 0 3
  change
    P0 * (Y * Y.conjTranspose) * P0 =
      P0 - T * T.conjTranspose - P0 * Δ * P0 ∧
    P3 * (Y * Y.conjTranspose) * P3 =
      P3 - T.conjTranspose * T - P3 * Δ * P3
  have hP02 : P0 * P0 = P0 := by
    simpa only [P0, sixTruthFibreProjection, sixTruthSectorProjection]
      using (sixTruthSectorProjection_idempotent label
        (fun u : Fin 4 => u = 0))
  have hP32 : P3 * P3 = P3 := by
    simpa only [P3, sixTruthFibreProjection, sixTruthSectorProjection]
      using (sixTruthSectorProjection_idempotent label
        (fun u : Fin 4 => u = 3))
  have hP0H : P0.IsHermitian := by
    simpa only [P0, sixTruthFibreProjection, sixTruthSectorProjection]
      using sixTruthSectorProjection_isHermitian label
        (fun u : Fin 4 => u = 0)
  have hP3H : P3.IsHermitian := by
    simpa only [P3, sixTruthFibreProjection, sixTruthSectorProjection]
      using sixTruthSectorProjection_isHermitian label
        (fun u : Fin 4 => u = 3)
  obtain ⟨hPR, hRP⟩ := sixOpposite03_fibreProjections_orthogonal label
  have hC : C = P0 + P3 :=
    sixPlus_complement_eq_oppositeFibreProjections label
  have hPT : P0 * T = T := by
    change P0 * (((2 : ℂ) * Complex.I) • (P0 * D * P3)) =
      ((2 : ℂ) * Complex.I) • (P0 * D * P3)
    rw [Matrix.mul_smul]
    congr 1
    calc
      P0 * (P0 * D * P3) = (P0 * P0) * D * P3 := by
        noncomm_ring
      _ = P0 * D * P3 := by rw [hP02]
  have hTR : T * P3 = T := by
    change (((2 : ℂ) * Complex.I) • (P0 * D * P3)) * P3 =
      ((2 : ℂ) * Complex.I) • (P0 * D * P3)
    rw [Matrix.smul_mul]
    congr 1
    calc
      (P0 * D * P3) * P3 = P0 * D * (P3 * P3) := by
        noncomm_ring
      _ = P0 * D * P3 := by rw [hP32]
  have hBlock := sixLabelled_plusWitness_nonSaturated_blockDefect
    label D hD
  change X * X + Y * Y.conjTranspose = C - C * Δ * C ∧
    X * Y = -(C * Δ * Q) ∧
    Y.conjTranspose * Y = Q - Q * Δ * Q at hBlock
  have hX : X * X = T * T.conjTranspose +
      T.conjTranspose * T := by
    have h := sixLabelled_exactHamming_saturated03_cornerSquare_oppositeGram
      label D hD
    change X * X = T * T.conjTranspose + T.conjTranspose * T at h
    exact h
  have hGram : Y * Y.conjTranspose + T * T.conjTranspose +
      T.conjTranspose * T = C - C * Δ * C := by
    calc
      Y * Y.conjTranspose + T * T.conjTranspose +
          T.conjTranspose * T = X * X + Y * Y.conjTranspose := by
            rw [hX]
            abel
      _ = C - C * Δ * C := hBlock.1
  exact sixMatrix_twoFibre_neutralGram_perturbedCompressions
    P0 P3 T (Y * Y.conjTranspose) C Δ
    hP02 hP32 hP0H hP3H hPR hRP hPT hTR hC hGram


/-- The two transition traces in one output-fibre row sum to
the trace of the complete neutral-exchange row. -/
theorem sixMatrix_transitionTrace_rowSum
    (P Y N M : SixMat) (hInput : Y * (N + M) = Y) :
    sixMatrix_transitionTrace P Y N +
      sixMatrix_transitionTrace P Y M =
      (P * Y * Y.conjTranspose).trace := by
  unfold sixMatrix_transitionTrace
  rw [← Matrix.trace_add]
  congr 1
  calc
    P * Y * N * Y.conjTranspose +
        P * Y * M * Y.conjTranspose =
        P * (Y * (N + M)) * Y.conjTranspose := by noncomm_ring
    _ = P * Y * Y.conjTranspose := by rw [hInput]

/-- Both output-fibre contributions to one neutral input column
sum to the full neutral-input Gram trace. -/
theorem sixMatrix_transitionTrace_columnSum
    (P R Y N : SixMat) (hOutput : (P + R) * Y = Y) :
    sixMatrix_transitionTrace P Y N +
      sixMatrix_transitionTrace R Y N =
      (Y * N * Y.conjTranspose).trace := by
  unfold sixMatrix_transitionTrace
  rw [← Matrix.trace_add]
  congr 1
  calc
    P * Y * N * Y.conjTranspose +
        R * Y * N * Y.conjTranspose =
        ((P + R) * Y) * N * Y.conjTranspose := by noncomm_ring
    _ = Y * N * Y.conjTranspose := by rw [hOutput]

/-- The original nonsaturated Dirac transition table has exact
row and column defect equations. In the output equations,
E03 is the genuine oriented squared 00/11 Dirac energy.
The four column- and row-trace terms are actual six-by-six
complex matrix traces, without choosing a basis or assuming
Pauli saturation. -/
theorem sixLabelled_plusWitness_nonsaturated_transitionTable_traceIdentities
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    let Y := C * W * Q
    let Δ := (1 : SixMat) - W * W
    let P0 := sixTruthFibreProjection label 0
    let P3 := sixTruthFibreProjection label 3
    let N1 := sixTruthFibreProjection label 1
    let N2 := sixTruthFibreProjection label 2
    let a := sixMatrix_transitionTrace P0 Y N1
    let b := sixMatrix_transitionTrace P0 Y N2
    let c := sixMatrix_transitionTrace P3 Y N1
    let d := sixMatrix_transitionTrace P3 Y N2
    (a + b + (P0 * Δ * P0).trace =
      (truthMultiplicity label 0 : ℂ) -
        4 * ((sixTruthFibreBlockEnergy label D 0 3 : ℝ) : ℂ) ∧
     c + d + (P3 * Δ * P3).trace =
      (truthMultiplicity label 3 : ℂ) -
        4 * ((sixTruthFibreBlockEnergy label D 0 3 : ℝ) : ℂ)) ∧
    (a + c + (N1 * Δ * N1).trace =
      (truthMultiplicity label 1 : ℂ) ∧
     b + d + (N2 * Δ * N2).trace =
      (truthMultiplicity label 2 : ℂ)) := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let Y : SixMat := C * W * Q
  let Δ : SixMat := 1 - W * W
  let P0 : SixMat := sixTruthFibreProjection label 0
  let P3 : SixMat := sixTruthFibreProjection label 3
  let N1 : SixMat := sixTruthFibreProjection label 1
  let N2 : SixMat := sixTruthFibreProjection label 2
  let T : SixMat := ((2 : ℂ) * Complex.I) •
    sixTruthFibreBlock label D 0 3
  let e : ℝ := sixTruthFibreBlockEnergy label D 0 3
  let a : ℂ := sixMatrix_transitionTrace P0 Y N1
  let b : ℂ := sixMatrix_transitionTrace P0 Y N2
  let c : ℂ := sixMatrix_transitionTrace P3 Y N1
  let d : ℂ := sixMatrix_transitionTrace P3 Y N2
  change
    (a + b + (P0 * Δ * P0).trace =
        (truthMultiplicity label 0 : ℂ) - 4 * (e : ℂ) ∧
     c + d + (P3 * Δ * P3).trace =
        (truthMultiplicity label 3 : ℂ) - 4 * (e : ℂ)) ∧
    (a + c + (N1 * Δ * N1).trace =
        (truthMultiplicity label 1 : ℂ) ∧
     b + d + (N2 * Δ * N2).trace =
        (truthMultiplicity label 2 : ℂ))
  have hP02 : P0 * P0 = P0 := by
    simpa only [P0, sixTruthFibreProjection, sixTruthSectorProjection]
      using (sixTruthSectorProjection_idempotent label
        (fun u : Fin 4 => u = 0))
  have hP32 : P3 * P3 = P3 := by
    simpa only [P3, sixTruthFibreProjection, sixTruthSectorProjection]
      using (sixTruthSectorProjection_idempotent label
        (fun u : Fin 4 => u = 3))
  have hN12 : N1 * N1 = N1 := by
    simpa only [N1, sixTruthFibreProjection, sixTruthSectorProjection]
      using (sixTruthSectorProjection_idempotent label
        (fun u : Fin 4 => u = 1))
  have hN22 : N2 * N2 = N2 := by
    simpa only [N2, sixTruthFibreProjection, sixTruthSectorProjection]
      using (sixTruthSectorProjection_idempotent label
        (fun u : Fin 4 => u = 2))
  have hQ2 : Q * Q = Q :=
    sixTruthSectorProjection_idempotent label squarePlusNeutral
  have hQH : Q.IsHermitian :=
    sixTruthSectorProjection_isHermitian label squarePlusNeutral
  have hN1H : N1.IsHermitian := by
    simpa only [N1, sixTruthFibreProjection, sixTruthSectorProjection]
      using sixTruthSectorProjection_isHermitian label
        (fun u : Fin 4 => u = 1)
  have hN2H : N2.IsHermitian := by
    simpa only [N2, sixTruthFibreProjection, sixTruthSectorProjection]
      using sixTruthSectorProjection_isHermitian label
        (fun u : Fin 4 => u = 2)
  have hQsplit : Q = N1 + N2 :=
    sixPlusNeutral_eq_fibre01_add_fibre10 label
  have hCsplit : C = P0 + P3 :=
    sixPlus_complement_eq_oppositeFibreProjections label
  have hC2 : C * C = C := by
    change (1 - Q) * (1 - Q) = 1 - Q
    calc
      (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q := by noncomm_ring
      _ = 1 - Q := by rw [hQ2]; abel
  have hInput : Y * (N1 + N2) = Y := by
    rw [← hQsplit]
    change (C * W * Q) * Q = C * W * Q
    calc
      (C * W * Q) * Q = C * W * (Q * Q) := by noncomm_ring
      _ = C * W * Q := by rw [hQ2]
  have hOutput : (P0 + P3) * Y = Y := by
    rw [← hCsplit]
    change C * (C * W * Q) = C * W * Q
    calc
      C * (C * W * Q) = (C * C) * W * Q := by noncomm_ring
      _ = C * W * Q := by rw [hC2]
  have hRows := sixLabelled_plusWitness_nonsaturated_fibreNeutralGram
    label D hD
  change
    P0 * (Y * Y.conjTranspose) * P0 =
      P0 - T * T.conjTranspose - P0 * Δ * P0 ∧
    P3 * (Y * Y.conjTranspose) * P3 =
      P3 - T.conjTranspose * T - P3 * Δ * P3 at hRows
  have hP0tr : P0.trace = (truthMultiplicity label 0 : ℂ) := by
    have h := sixTruthSectorProjection_trace_eq_card label
      (fun u : Fin 4 => u = 0)
    change P0.trace = (truthMultiplicity label 0 : ℂ) at h
    exact h
  have hP3tr : P3.trace = (truthMultiplicity label 3 : ℂ) := by
    have h := sixTruthSectorProjection_trace_eq_card label
      (fun u : Fin 4 => u = 3)
    change P3.trace = (truthMultiplicity label 3 : ℂ) at h
    exact h
  have hN1tr : N1.trace = (truthMultiplicity label 1 : ℂ) := by
    have h := sixTruthSectorProjection_trace_eq_card label
      (fun u : Fin 4 => u = 1)
    change N1.trace = (truthMultiplicity label 1 : ℂ) at h
    exact h
  have hN2tr : N2.trace = (truthMultiplicity label 2 : ℂ) := by
    have h := sixTruthSectorProjection_trace_eq_card label
      (fun u : Fin 4 => u = 2)
    change N2.trace = (truthMultiplicity label 2 : ℂ) at h
    exact h
  have hTgram : T * T.conjTranspose =
      (4 : ℂ) • ((sixTruthFibreBlock label D 0 3) *
        (sixTruthFibreBlock label D 0 3).conjTranspose) :=
    sixMatrix_positiveDoubleImagGram
      (sixTruthFibreBlock label D 0 3)
  have hTtr : (T * T.conjTranspose).trace = 4 * (e : ℂ) := by
    rw [hTgram, Matrix.trace_smul,
      sixTruthFibreBlock_gram_trace_eq_energy]
    simp [e, smul_eq_mul]
  have hTrevtr : (T.conjTranspose * T).trace = 4 * (e : ℂ) := by
    calc
      _ = (T * T.conjTranspose).trace :=
        Matrix.trace_mul_comm T.conjTranspose T
      _ = 4 * (e : ℂ) := hTtr
  have hRow0 : a + b + (P0 * Δ * P0).trace =
      (truthMultiplicity label 0 : ℂ) - 4 * (e : ℂ) := by
    have hSum := sixMatrix_transitionTrace_rowSum
      P0 Y N1 N2 hInput
    change a + b = (P0 * Y * Y.conjTranspose).trace at hSum
    rw [hSum]
    calc
      (P0 * Y * Y.conjTranspose).trace +
          (P0 * Δ * P0).trace =
        (P0 * (Y * Y.conjTranspose) * P0).trace +
          (P0 * Δ * P0).trace := by
            rw [← Matrix.mul_assoc]
            rw [sixMatrix_trace_doubleCompression_eq_leftCompression
              P0 (Y * Y.conjTranspose) hP02]
      _ = (P0 - T * T.conjTranspose - P0 * Δ * P0).trace +
          (P0 * Δ * P0).trace := by rw [hRows.1]
      _ = (truthMultiplicity label 0 : ℂ) - 4 * (e : ℂ) := by
        rw [Matrix.trace_sub, Matrix.trace_sub, hP0tr, hTtr]
        ring
  have hRow3 : c + d + (P3 * Δ * P3).trace =
      (truthMultiplicity label 3 : ℂ) - 4 * (e : ℂ) := by
    have hSum := sixMatrix_transitionTrace_rowSum
      P3 Y N1 N2 hInput
    change c + d = (P3 * Y * Y.conjTranspose).trace at hSum
    rw [hSum]
    calc
      (P3 * Y * Y.conjTranspose).trace +
          (P3 * Δ * P3).trace =
        (P3 * (Y * Y.conjTranspose) * P3).trace +
          (P3 * Δ * P3).trace := by
            rw [← Matrix.mul_assoc]
            rw [sixMatrix_trace_doubleCompression_eq_leftCompression
              P3 (Y * Y.conjTranspose) hP32]
      _ = (P3 - T.conjTranspose * T - P3 * Δ * P3).trace +
          (P3 * Δ * P3).trace := by rw [hRows.2]
      _ = (truthMultiplicity label 3 : ℂ) - 4 * (e : ℂ) := by
        rw [Matrix.trace_sub, Matrix.trace_sub, hP3tr, hTrevtr]
        ring
  have hQNs := sixPlusNeutral_mul_fibre1_or_fibre2 label
  change Q * N1 = N1 ∧ Q * N2 = N2 at hQNs
  have hN1Q : N1 * Q = N1 := by
    have h := congrArg Matrix.conjTranspose hQNs.1
    simpa only [Matrix.conjTranspose_mul, hN1H.eq, hQH.eq] using h
  have hN2Q : N2 * Q = N2 := by
    have h := congrArg Matrix.conjTranspose hQNs.2
    simpa only [Matrix.conjTranspose_mul, hN2H.eq, hQH.eq] using h
  have hDef := sixLabelled_plusWitness_nonSaturated_blockDefect
    label D hD
  change
    (C * W * C) * (C * W * C) + Y * Y.conjTranspose =
      C - C * Δ * C ∧
    (C * W * C) * Y = -(C * Δ * Q) ∧
    Y.conjTranspose * Y = Q - Q * Δ * Q at hDef
  have hCol1 := sixMatrix_neutralColumnTrace_defect
    Y Q N1 Δ hN12 hQNs.1 hN1Q hDef.2.2
  have hCol2 := sixMatrix_neutralColumnTrace_defect
    Y Q N2 Δ hN22 hQNs.2 hN2Q hDef.2.2
  have hColSum1 := sixMatrix_transitionTrace_columnSum
    P0 P3 Y N1 hOutput
  change a + c = (Y * N1 * Y.conjTranspose).trace at hColSum1
  have hColSum2 := sixMatrix_transitionTrace_columnSum
    P0 P3 Y N2 hOutput
  change b + d = (Y * N2 * Y.conjTranspose).trace at hColSum2
  constructor
  · exact ⟨hRow0, hRow3⟩
  · constructor
    · rw [hColSum1]
      rw [hN1tr] at hCol1
      exact hCol1
    · rw [hColSum2]
      rw [hN2tr] at hCol2
      exact hCol2

end Neoplatonic.LTR
