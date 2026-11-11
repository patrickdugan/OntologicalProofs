import Neoplatonic.LTR.SixDimensionalSaturated03TwoDefectChannels
import Neoplatonic.LTR.SixDimensionalSaturated03Singleton11NoGo
import Neoplatonic.LTR.SixDimensionalSignedFibreNeutralGram
import Neoplatonic.LTR.SixDimensionalSignedWitnessPartialIsometry
import Mathlib.Tactic

/-!
# LTR-MAN-117: true two-by-two neutral-channel transition energies

MAN-113 gives the original-coordinate two-channel decomposition of
the neutral exchange at pure positive saturation. Each doubled output
truth fibre has one available rank-one channel, while the neutral
truth fibres 01,10 are one-dimensional.

Instead of choosing basis vectors, define four transition energies
as complex traces

  e_uv = Tr(P_u Y N_v Yᴴ),

with u in {00,11} and v in {01,10}. The exact isometry YᴴY=Q
and corner support CY=Y give column sums one. Each doubled output
fibre has neutral Gram compression of trace one by MAN-104/96,
giving row sums one.

Thus the transition table is doubly stochastic and, in its
two-by-two form, its opposite entries agree. These equalities are
fully proved in the original 6x6 Hilbert coordinates without
choosing a U(2) basis.

Proving nonnegativity and relating this overlap table to coordinate
operator norms are the remaining steps toward the full 2+2 no-go.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal ComplexOrder

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The transition energy from neutral input fibre N into the
output corner fibre P, expressed without selecting basis vectors. -/
def sixMatrix_transitionTrace (P Y N : SixMat) : ℂ :=
  (P * Y * N * Y.conjTranspose).trace

/-- An exact 2x2 doubly stochastic table has equal diagonal
entries and equal off-diagonal entries over the complex field. -/
theorem twoByTwo_complex_bistochastic_oppositeEqual
    (a b c d : ℂ)
    (hrow0 : a + b = 1) (hrow1 : c + d = 1)
    (hcol0 : a + c = 1) (hcol1 : b + d = 1) :
    a = d ∧ b = c := by
  constructor
  · linear_combination hrow0 - hcol1
  · linear_combination hrow0 - hcol0

/-- A partial-isometry exchange with two corner/neutral
partitions and unit row and column traces yields an exact
bistochastic table of four matrix overlap traces. -/
theorem sixMatrix_twoByTwo_transitionTrace_bistochastic
    (P R N M Y : SixMat)
    (hInput : Y * (N + M) = Y)
    (hOutput : (P + R) * Y = Y)
    (hRowP : (P * Y * Y.conjTranspose).trace = 1)
    (hRowR : (R * Y * Y.conjTranspose).trace = 1)
    (hColN : (Y * N * Y.conjTranspose).trace = 1)
    (hColM : (Y * M * Y.conjTranspose).trace = 1) :
    let a := sixMatrix_transitionTrace P Y N
    let b := sixMatrix_transitionTrace P Y M
    let c := sixMatrix_transitionTrace R Y N
    let d := sixMatrix_transitionTrace R Y M
    (a + b = 1 ∧ c + d = 1) ∧
      (a + c = 1 ∧ b + d = 1) ∧
      (a = d ∧ b = c) := by
  dsimp only [sixMatrix_transitionTrace]
  have hRow (S : SixMat)
      (hS : (S * Y * Y.conjTranspose).trace = (1 : ℂ)) :
      (S * Y * N * Y.conjTranspose).trace +
        (S * Y * M * Y.conjTranspose).trace = (1 : ℂ) := by
    rw [← Matrix.trace_add]
    have heq : S * Y * N * Y.conjTranspose +
        S * Y * M * Y.conjTranspose =
          S * Y * Y.conjTranspose := by
      calc
        _ = S * (Y * (N + M)) * Y.conjTranspose := by noncomm_ring
        _ = S * Y * Y.conjTranspose := by rw [hInput]
    rw [heq]
    exact hS
  have hCol (S : SixMat)
      (hS : (Y * S * Y.conjTranspose).trace = (1 : ℂ)) :
      (P * Y * S * Y.conjTranspose).trace +
        (R * Y * S * Y.conjTranspose).trace = (1 : ℂ) := by
    rw [← Matrix.trace_add]
    have heq : P * Y * S * Y.conjTranspose +
        R * Y * S * Y.conjTranspose =
          Y * S * Y.conjTranspose := by
      calc
        _ = ((P + R) * Y) * S * Y.conjTranspose := by noncomm_ring
        _ = Y * S * Y.conjTranspose := by rw [hOutput]
    rw [heq]
    exact hS
  have hr0 := hRow P hRowP
  have hr1 := hRow R hRowR
  have hc0 := hCol N hColN
  have hc1 := hCol M hColM
  exact ⟨⟨hr0, hr1⟩, ⟨hc0, hc1⟩,
    twoByTwo_complex_bistochastic_oppositeEqual _ _ _ _
      hr0 hr1 hc0 hc1⟩

/-- The neutral sector of the positive signed witness is
exactly the sum of the 01 and 10 truth-fibre projections. -/
theorem sixPlusNeutral_eq_fibre01_add_fibre10
    (label : Fin 6 → Fin 4) :
    sixTruthSectorProjection label squarePlusNeutral =
      sixTruthFibreProjection label 1 +
        sixTruthFibreProjection label 2 := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    generalize hli : label i = u
    fin_cases u <;>
      simp [sixTruthSectorProjection, sixTruthFibreProjection,
        squarePlusNeutral, Matrix.add_apply,
        Matrix.diagonal_apply, hli]
  · simp [sixTruthSectorProjection, sixTruthFibreProjection,
      Matrix.add_apply, Matrix.diagonal_apply, hij]

/-- A finite complex idempotent compression has the same
trace as the single-sided compression. -/
theorem sixMatrix_trace_doubleCompression_eq_leftCompression
    (P M : SixMat) (hPid : P * P = P) :
    (P * M * P).trace = (P * M).trace := by
  calc
    (P * M * P).trace = (P * (P * M)).trace :=
      Matrix.trace_mul_comm (P * M) P
    _ = ((P * P) * M).trace := by rw [Matrix.mul_assoc]
    _ = (P * M).trace := by rw [hPid]

/-- For an isometric neutral-to-corner map, the trace of an
input-fibre column Gram equals that fibre's trace. -/
theorem sixMatrix_isometry_columnTrace
    (Y Q N : SixMat)
    (hIsom : Y.conjTranspose * Y = Q)
    (hQN : Q * N = N)
    (hN : N.trace = (1 : ℂ)) :
    (Y * N * Y.conjTranspose).trace = (1 : ℂ) := by
  calc
    (Y * N * Y.conjTranspose).trace =
        (Y.conjTranspose * (Y * N)).trace :=
          Matrix.trace_mul_comm (Y * N) Y.conjTranspose
    _ = (Q * N).trace := by rw [← Matrix.mul_assoc, hIsom]
    _ = N.trace := by rw [hQN]
    _ = 1 := hN

/-- The positive neutral-sector projection acts identically
on either singleton input truth-fibre projection. -/
theorem sixPlusNeutral_mul_fibre1_or_fibre2
    (label : Fin 6 → Fin 4) :
    sixTruthSectorProjection label squarePlusNeutral *
        sixTruthFibreProjection label 1 =
          sixTruthFibreProjection label 1 ∧
      sixTruthSectorProjection label squarePlusNeutral *
        sixTruthFibreProjection label 2 =
          sixTruthFibreProjection label 2 := by
  constructor
  · ext i j
    simp only [sixTruthSectorProjection, sixTruthFibreProjection,
      Matrix.diagonal_mul]
    by_cases hi : label i = 1 <;>
      simp [hi, squarePlusNeutral, Matrix.diagonal_apply]
  · ext i j
    simp only [sixTruthSectorProjection, sixTruthFibreProjection,
      Matrix.diagonal_mul]
    by_cases hi : label i = 2 <;>
      simp [hi, squarePlusNeutral, Matrix.diagonal_apply]

/-- In the genuine pure-positive saturated 2+2 Hamming chart,
the 00/11 output-to-01/10 input neutral exchange overlap traces
form an exact 2x2 bistochastic table. -/
theorem sixLabelled_exactHamming_saturated03_oppositeDouble_transitionTrace
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ))
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = 0) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    let Y := C * W * Q
    let P0 := sixTruthFibreProjection label 0
    let P3 := sixTruthFibreProjection label 3
    let N1 := sixTruthFibreProjection label 1
    let N2 := sixTruthFibreProjection label 2
    let a := sixMatrix_transitionTrace P0 Y N1
    let b := sixMatrix_transitionTrace P0 Y N2
    let c := sixMatrix_transitionTrace P3 Y N1
    let d := sixMatrix_transitionTrace P3 Y N2
    (a + b = 1 ∧ c + d = 1) ∧
      (a + c = 1 ∧ b + d = 1) ∧
      (a = d ∧ b = c) := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let Y : SixMat := C * W * Q
  let P0 : SixMat := sixTruthFibreProjection label 0
  let P3 : SixMat := sixTruthFibreProjection label 3
  let N1 : SixMat := sixTruthFibreProjection label 1
  let N2 : SixMat := sixTruthFibreProjection label 2
  let B : SixMat := sixTruthFibreBlock label D 0 3
  let T : SixMat := ((2 : ℂ) * Complex.I) • B
  change
    ((sixMatrix_transitionTrace P0 Y N1 +
      sixMatrix_transitionTrace P0 Y N2 = 1) ∧
      (sixMatrix_transitionTrace P3 Y N1 +
        sixMatrix_transitionTrace P3 Y N2 = 1)) ∧
    ((sixMatrix_transitionTrace P0 Y N1 +
      sixMatrix_transitionTrace P3 Y N1 = 1) ∧
      (sixMatrix_transitionTrace P0 Y N2 +
        sixMatrix_transitionTrace P3 Y N2 = 1)) ∧
      (sixMatrix_transitionTrace P0 Y N1 =
        sixMatrix_transitionTrace P3 Y N2 ∧
        sixMatrix_transitionTrace P0 Y N2 =
          sixMatrix_transitionTrace P3 Y N1)
  obtain ⟨hm0, hm1, hm2, hm3⟩ :=
    sixLabelled_exactHamming_saturated03_onlyOppositeDoubles
      label D hsurj hD hham h03 h12
  have hP02 : P0 * P0 = P0 := by
    simpa only [P0, sixTruthFibreProjection, sixTruthSectorProjection] using
      sixTruthSectorProjection_idempotent label
        (fun u : Fin 4 => u = 0)
  have hP32 : P3 * P3 = P3 := by
    simpa only [P3, sixTruthFibreProjection, sixTruthSectorProjection] using
      sixTruthSectorProjection_idempotent label
        (fun u : Fin 4 => u = 3)
  have hQ2 : Q * Q = Q :=
    sixTruthSectorProjection_idempotent label squarePlusNeutral
  have hC2 : C * C = C := by
    change (1 - Q) * (1 - Q) = 1 - Q
    calc
      (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q := by noncomm_ring
      _ = 1 - Q := by rw [hQ2]; abel
  have hQsplit : Q = N1 + N2 :=
    sixPlusNeutral_eq_fibre01_add_fibre10 label
  have hCsplit : C = P0 + P3 :=
    sixPlus_complement_eq_oppositeFibreProjections label
  have hYQ : Y * Q = Y := by
    dsimp [Y]
    calc
      ((1 - Q) * W * Q) * Q =
          (1 - Q) * W * (Q * Q) := by noncomm_ring
      _ = (1 - Q) * W * Q := by rw [hQ2]
  have hInput : Y * (N1 + N2) = Y := by
    rw [← hQsplit]
    exact hYQ
  have hOutput : (P0 + P3) * Y = Y := by
    rw [← hCsplit]
    change C * (C * W * Q) = C * W * Q
    calc
      C * (C * W * Q) = (C * C) * W * Q := by noncomm_ring
      _ = C * W * Q := by rw [hC2]
  have hIsom : Y.conjTranspose * Y = Q := by
    have h := (sixLabelled_exactHamming_saturated03_partialIsometry
      label D hD hham h03 h12).2.2
    change Y.conjTranspose * Y = Q at h
    exact h
  obtain ⟨hQN1, hQN2⟩ :=
    sixPlusNeutral_mul_fibre1_or_fibre2 label
  have hN1trace : N1.trace = (1 : ℂ) := by
    have h := sixTruthSectorProjection_trace_eq_card label
      (fun u : Fin 4 => u = 1)
    change N1.trace = (truthMultiplicity label 1 : ℂ) at h
    simpa [hm1] using h
  have hN2trace : N2.trace = (1 : ℂ) := by
    have h := sixTruthSectorProjection_trace_eq_card label
      (fun u : Fin 4 => u = 2)
    change N2.trace = (truthMultiplicity label 2 : ℂ) at h
    simpa [hm2] using h
  have hColN1 : (Y * N1 * Y.conjTranspose).trace = 1 :=
    sixMatrix_isometry_columnTrace Y Q N1 hIsom hQN1 hN1trace
  have hColN2 : (Y * N2 * Y.conjTranspose).trace = 1 :=
    sixMatrix_isometry_columnTrace Y Q N2 hIsom hQN2 hN2trace
  have hP0trace : P0.trace = (2 : ℂ) := by
    have h := sixTruthSectorProjection_trace_eq_card label
      (fun u : Fin 4 => u = 0)
    change P0.trace = (truthMultiplicity label 0 : ℂ) at h
    simpa [hm0] using h
  have hP3trace : P3.trace = (2 : ℂ) := by
    have h := sixTruthSectorProjection_trace_eq_card label
      (fun u : Fin 4 => u = 3)
    change P3.trace = (truthMultiplicity label 3 : ℂ) at h
    simpa [hm3] using h
  have hGram := (sixLabelled_exactHamming_saturated03_oppositeBlock_quarterGram
    label D hD hham h03 h12).2
  change (((4 : ℂ) • (B * B.conjTranspose)).trace = 1) at hGram
  have hTgram : T * T.conjTranspose =
      (4 : ℂ) • (B * B.conjTranspose) :=
    sixMatrix_positiveDoubleImagGram B
  have hTtrace : (T * T.conjTranspose).trace = (1 : ℂ) := by
    rw [hTgram]
    exact hGram
  have hTrevTrace : (T.conjTranspose * T).trace = (1 : ℂ) := by
    calc
      _ = (T * T.conjTranspose).trace :=
        (Matrix.trace_mul_comm T T.conjTranspose).symm
      _ = 1 := hTtrace
  have hFibre := sixLabelled_exactHamming_saturated03_fibreNeutralGram
    label D hD hham h03 h12
  change P0 * (Y * Y.conjTranspose) * P0 =
      P0 - T * T.conjTranspose ∧
    P3 * (Y * Y.conjTranspose) * P3 =
      P3 - T.conjTranspose * T at hFibre
  have hRowP : (P0 * Y * Y.conjTranspose).trace = (1 : ℂ) := by
    calc
      (P0 * Y * Y.conjTranspose).trace =
        (P0 * (Y * Y.conjTranspose) * P0).trace := by
          simpa only [Matrix.mul_assoc] using
            (sixMatrix_trace_doubleCompression_eq_leftCompression
              P0 (Y * Y.conjTranspose) hP02).symm
      _ = (P0 - T * T.conjTranspose).trace := by rw [hFibre.1]
      _ = 1 := by rw [Matrix.trace_sub, hP0trace, hTtrace]; norm_num
  have hRowR : (P3 * Y * Y.conjTranspose).trace = (1 : ℂ) := by
    calc
      (P3 * Y * Y.conjTranspose).trace =
        (P3 * (Y * Y.conjTranspose) * P3).trace := by
          simpa only [Matrix.mul_assoc] using
            (sixMatrix_trace_doubleCompression_eq_leftCompression
              P3 (Y * Y.conjTranspose) hP32).symm
      _ = (P3 - T.conjTranspose * T).trace := by rw [hFibre.2]
      _ = 1 := by rw [Matrix.trace_sub, hP3trace, hTrevTrace]; norm_num
  exact sixMatrix_twoByTwo_transitionTrace_bistochastic
    P0 P3 N1 N2 Y hInput hOutput
      hRowP hRowR hColN1 hColN2

end Neoplatonic.LTR
