import Neoplatonic.LTR.SixDimensionalOffDiagonalNeutralEdgeOrthogonality
import Neoplatonic.LTR.SixDimensionalSignedFibreNeutralGram
import Mathlib.Tactic

/-!
# LTR-MAN-124: the real six-coordinate positive corner is off-diagonal

The abstract MAN-123 theorem requires an off-diagonal opposite-truth
corner X=P0 X P3 + P3 X P0. Here this premise is discharged for the
actual six-dimensional labelled positive Hamming commutator W=A+B.

The key finite observation is that an imaginary Dirac commutator with
a diagonal truth function has no same-truth-fibre entries. Hence the
00 and 11 self-blocks of W vanish identically. Complementing the
01/10 neutral projector and applying elementary corner algebra
proves the off-diagonal identity with no saturation assumptions.

The final theorem combines it with MAN-94's actual partial-isometry
XY=0 to split the two original six-dimensional output-fibre rows.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A corner made of two orthogonal idempotent fibres, with
vanishing self-couplings, contains only its cross-fibre blocks. -/
theorem sixMatrix_corner_offdiagonal_of_zeroSelfBlocks
    (P R W : SixMat)
    (hPP : P * P = P) (hRR : R * R = R)
    (hPR : P * R = 0) (hRP : R * P = 0)
    (hPWP : P * W * P = 0) (hRWR : R * W * R = 0) :
    let X := (P + R) * W * (P + R)
    X = P * X * R + R * X * P := by
  dsimp only
  have hPC : P * (P + R) = P := by
    calc
      P * (P + R) = P * P + P * R := by noncomm_ring
      _ = P := by rw [hPP, hPR]; simp
  have hCR : (P + R) * R = R := by
    calc
      (P + R) * R = P * R + R * R := by noncomm_ring
      _ = R := by rw [hPR, hRR]; simp
  have hRC : R * (P + R) = R := by
    calc
      R * (P + R) = R * P + R * R := by noncomm_ring
      _ = R := by rw [hRP, hRR]; simp
  have hCP : (P + R) * P = P := by
    calc
      (P + R) * P = P * P + R * P := by noncomm_ring
      _ = P := by rw [hPP, hRP]; simp
  have hPXR :
      P * ((P + R) * W * (P + R)) * R = P * W * R := by
    calc
      P * ((P + R) * W * (P + R)) * R =
          (P * (P + R)) * W * ((P + R) * R) := by noncomm_ring
      _ = P * W * R := by rw [hPC, hCR]
  have hRXP :
      R * ((P + R) * W * (P + R)) * P = R * W * P := by
    calc
      R * ((P + R) * W * (P + R)) * P =
          (R * (P + R)) * W * ((P + R) * P) := by noncomm_ring
      _ = R * W * P := by rw [hRC, hCP]
  calc
    (P + R) * W * (P + R) =
        P * W * P + P * W * R + R * W * P + R * W * R := by
          noncomm_ring
    _ = P * W * R + R * W * P := by rw [hPWP, hRWR]; abel
    _ = P * ((P + R) * W * (P + R)) * R +
          R * ((P + R) * W * (P + R)) * P := by
            rw [hPXR, hRXP]

/-- Every self-truth fibre block of the actual positive signed
Dirac commutator is identically zero, for arbitrary labels and D. -/
theorem sixLabelled_plusWitness_selfFibre_zero
    (label : Fin 6 → Fin 4) (D : SixMat) (u : Fin 4) :
    sixTruthFibreBlock label
      (labelledSquareA label D + labelledSquareB label D) u u = 0 := by
  ext i j
  rw [sixTruthFibreBlock_entry]
  by_cases hi : label i = u
  · by_cases hj : label j = u
    · simp [hi, hj, Matrix.add_apply, labelledSquareA, labelledSquareB]
    · simp [hj]
  · simp [hi]

/-- The true 00/11 positive-signed corner lies entirely in its
two opposite directed truth-fibre blocks, without selecting a
canonical singular-vector basis. -/
theorem sixLabelled_plusWitness_actualCorner_offdiagonal
    (label : Fin 6 → Fin 4) (D : SixMat) :
    let W := labelledSquareA label D + labelledSquareB label D
    let Q := sixTruthSectorProjection label squarePlusNeutral
    let C := (1 - Q : SixMat)
    let X := C * W * C
    let P := sixTruthFibreProjection label 0
    let R := sixTruthFibreProjection label 3
    X = P * X * R + R * X * P := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let P : SixMat := sixTruthFibreProjection label 0
  let R : SixMat := sixTruthFibreProjection label 3
  change C * W * C = P * (C * W * C) * R + R * (C * W * C) * P
  have hPP : P * P = P := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label (fun u : Fin 4 => u = 0))
  have hRR : R * R = R := by
    simpa only [R, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label (fun u : Fin 4 => u = 3))
  obtain ⟨hPR, hRP⟩ := sixOpposite03_fibreProjections_orthogonal label
  have hPWP : P * W * P = 0 := by
    change sixTruthFibreBlock label W 0 0 = 0
    exact sixLabelled_plusWitness_selfFibre_zero label D 0
  have hRWR : R * W * R = 0 := by
    change sixTruthFibreBlock label W 3 3 = 0
    exact sixLabelled_plusWitness_selfFibre_zero label D 3
  have hC : C = P + R :=
    sixPlus_complement_eq_oppositeFibreProjections label
  rw [hC]
  exact sixMatrix_corner_offdiagonal_of_zeroSelfBlocks
    P R W hPP hRR hPR hRP hPWP hRWR

/-- MAN-94's original-coordinates product XY=0 splits into the
individual 00 and 11 fibre outputs in the genuine six-dimensional
saturated Hamming Dirac representation. -/
theorem sixLabelled_exactHamming_saturated03_actualCorner_twoRows_zero
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
    let X := C * W * C
    let Y := C * W * Q
    let P := sixTruthFibreProjection label 0
    let R := sixTruthFibreProjection label 3
    X * P * Y = 0 ∧ X * R * Y = 0 := by
  dsimp only
  let W : SixMat := labelledSquareA label D + labelledSquareB label D
  let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
  let C : SixMat := 1 - Q
  let P : SixMat := sixTruthFibreProjection label 0
  let R : SixMat := sixTruthFibreProjection label 3
  let X : SixMat := C * W * C
  let Y : SixMat := C * W * Q
  change X * P * Y = 0 ∧ X * R * Y = 0
  have hPP : P * P = P := by
    simpa only [P, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label (fun u : Fin 4 => u = 0))
  have hRR : R * R = R := by
    simpa only [R, sixTruthFibreProjection, sixTruthSectorProjection] using
      (sixTruthSectorProjection_idempotent label (fun u : Fin 4 => u = 3))
  obtain ⟨hPR, hRP⟩ := sixOpposite03_fibreProjections_orthogonal label
  have hXoff : X = P * X * R + R * X * P :=
    sixLabelled_plusWitness_actualCorner_offdiagonal label D
  have hC : C = P + R :=
    sixPlus_complement_eq_oppositeFibreProjections label
  have hYrange : (P + R) * Y = Y := by
    have hC2 : C * C = C := by
      rw [hC]
      calc
        (P + R) * (P + R) =
            P * P + P * R + R * P + R * R := by noncomm_ring
        _ = P + R := by rw [hPP, hPR, hRP, hRR]; simp
    calc
      (P + R) * Y = C * (C * W * Q) := by rw [← hC]; rfl
      _ = (C * C) * W * Q := by noncomm_ring
      _ = Y := by rw [hC2]; rfl
  have hXY : X * Y = 0 := by
    have h := sixLabelled_exactHamming_saturated03_partialIsometry
      label D hD hham h03 h12
    change X * X + Y * Y.conjTranspose = C ∧
      X * Y = 0 ∧ Y.conjTranspose * Y = Q at h
    exact h.2.1
  exact sixMatrix_offdiagonal_XY_zero_split
    P R X Y hPP hRR hPR hRP hXoff hYrange hXY

end Neoplatonic.LTR
