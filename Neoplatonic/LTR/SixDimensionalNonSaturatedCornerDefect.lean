import Neoplatonic.LTR.SixDimensionalSignedWitnessPartialIsometry
import Mathlib.Tactic

/-!
# LTR-MAN-140: non-saturated signed witness corner-defect equations

MAN-94 treated a Hermitian signed Hamming witness satisfying W²=I.
In the non-saturated six-dimensional problem the positive signed
witness remains a contraction, but its residual 2x2 block may have
eigenvalues strictly between -1 and 1.

For any idempotent neutral projector Q with QWQ=0, define
  C = I-Q,  X=CWC,  Y=CWQ,  Z=QWC,  Δ=I-W².
The exact block identities are:
  X²+YZ = C-CΔC,        XY = -CΔQ,
  ZX = -QΔC,           ZY = Q-QΔQ.
When W and Q are Hermitian, Z=Y†, so
  X²+YY† = C-CΔC,     XY = -CΔQ,     Y†Y=Q-QΔQ.

These identities become MAN-94 when Δ=0, and hold for the actual
labelled positive signed Dirac witness under arbitrary energies.
They isolate the cross-channel obstruction to an explicit defect
supported by the residual signed-spectrum geometry.
-/

namespace Neoplatonic.LTR

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The exact four-block equations of an arbitrary signed witness,
with a spectral defect Δ=I-W². Saturation is not assumed. -/
theorem sixMatrix_zeroNeutral_fullBlockDefect
    (W Q : SixMat)
    (hQ : Q * Q = Q)
    (hQQ : Q * W * Q = 0) :
    let C : SixMat := 1 - Q
    let X : SixMat := C * W * C
    let Y : SixMat := C * W * Q
    let Z : SixMat := Q * W * C
    let Δ : SixMat := 1 - W * W
    X * X + Y * Z = C - C * Δ * C ∧
      X * Y = -(C * Δ * Q) ∧
      Z * X = -(Q * Δ * C) ∧
      Z * Y = Q - Q * Δ * Q := by
  let C : SixMat := 1 - Q
  let X : SixMat := C * W * C
  let Y : SixMat := C * W * Q
  let Z : SixMat := Q * W * C
  let Δ : SixMat := 1 - W * W
  change X * X + Y * Z = C - C * Δ * C ∧
    X * Y = -(C * Δ * Q) ∧
    Z * X = -(Q * Δ * C) ∧
    Z * Y = Q - Q * Δ * Q
  have hCC : C * C = C := by
    dsimp [C]
    calc
      (1 - Q) * (1 - Q) = 1 - Q - Q + Q * Q := by noncomm_ring
      _ = 1 - Q := by rw [hQ]; noncomm_ring
  have hCplus : C + Q = 1 := by
    dsimp [C]
    noncomm_ring
  have hCQ : C * Q = 0 := by
    dsimp [C]
    calc
      (1 - Q) * Q = Q - Q * Q := by noncomm_ring
      _ = 0 := by rw [hQ]; simp
  have hQC : Q * C = 0 := by
    dsimp [C]
    calc
      Q * (1 - Q) = Q - Q * Q := by noncomm_ring
      _ = 0 := by rw [hQ]; simp
  have hCWQWQ : C * W * Q * W * Q = 0 := by
    calc
      C * W * Q * W * Q = C * W * (Q * W * Q) := by noncomm_ring
      _ = 0 := by rw [hQQ]; simp
  have hQWQWC : Q * W * Q * W * C = 0 := by
    calc
      Q * W * Q * W * C = (Q * W * Q) * W * C := by noncomm_ring
      _ = 0 := by rw [hQQ]; simp
  have hQWQWQ : Q * W * Q * W * Q = 0 := by
    calc
      Q * W * Q * W * Q = (Q * W * Q) * W * Q := by noncomm_ring
      _ = 0 := by rw [hQQ]; simp
  have hXXYZ : X * X + Y * Z = C * W * W * C := by
    calc
      X * X + Y * Z = C * W * (C * C + Q * Q) * W * C := by
        dsimp [X, Y, Z]
        noncomm_ring
      _ = C * W * (C + Q) * W * C := by rw [hCC, hQ]
      _ = C * W * W * C := by rw [hCplus]; noncomm_ring
  have hXY : X * Y = C * W * W * Q := by
    calc
      X * Y = C * W * C * W * Q := by
        dsimp [X, Y]
        calc
          (C * W * C) * (C * W * Q) =
            C * W * (C * C) * W * Q := by noncomm_ring
          _ = C * W * C * W * Q := by rw [hCC]
      _ = C * W * (C + Q) * W * Q -
          C * W * Q * W * Q := by noncomm_ring
      _ = C * W * W * Q - C * W * Q * W * Q := by
        rw [hCplus]
        noncomm_ring
      _ = C * W * W * Q := by rw [hCWQWQ]; simp
  have hZX : Z * X = Q * W * W * C := by
    calc
      Z * X = Q * W * C * W * C := by
        dsimp [Z, X]
        calc
          (Q * W * C) * (C * W * C) =
            Q * W * (C * C) * W * C := by noncomm_ring
          _ = Q * W * C * W * C := by rw [hCC]
      _ = Q * W * (C + Q) * W * C -
          Q * W * Q * W * C := by noncomm_ring
      _ = Q * W * W * C - Q * W * Q * W * C := by
        rw [hCplus]
        noncomm_ring
      _ = Q * W * W * C := by rw [hQWQWC]; simp
  have hZY : Z * Y = Q * W * W * Q := by
    calc
      Z * Y = Q * W * C * W * Q := by
        dsimp [Z, Y]
        calc
          (Q * W * C) * (C * W * Q) =
            Q * W * (C * C) * W * Q := by noncomm_ring
          _ = Q * W * C * W * Q := by rw [hCC]
      _ = Q * W * (C + Q) * W * Q -
          Q * W * Q * W * Q := by noncomm_ring
      _ = Q * W * W * Q - Q * W * Q * W * Q := by
        rw [hCplus]
        noncomm_ring
      _ = Q * W * W * Q := by rw [hQWQWQ]; simp
  have hXXDefect : C * W * W * C = C - C * Δ * C := by
    dsimp [Δ]
    calc
      C * W * W * C = C * C - C * (1 - W * W) * C := by noncomm_ring
      _ = C - C * (1 - W * W) * C := by rw [hCC]
  have hXYDefect : C * W * W * Q = -(C * Δ * Q) := by
    dsimp [Δ]
    calc
      C * W * W * Q = C * W * W * Q - C * Q := by rw [hCQ]; simp
      _ = -(C * (1 - W * W) * Q) := by noncomm_ring
  have hZXDefect : Q * W * W * C = -(Q * Δ * C) := by
    dsimp [Δ]
    calc
      Q * W * W * C = Q * W * W * C - Q * C := by rw [hQC]; simp
      _ = -(Q * (1 - W * W) * C) := by noncomm_ring
  have hZYDefect : Q * W * W * Q = Q - Q * Δ * Q := by
    dsimp [Δ]
    calc
      Q * W * W * Q = Q * Q - Q * (1 - W * W) * Q := by noncomm_ring
      _ = Q - Q * (1 - W * W) * Q := by rw [hQ]
  exact ⟨hXXYZ.trans hXXDefect, hXY.trans hXYDefect,
    hZX.trans hZXDefect, hZY.trans hZYDefect⟩

/-- For Hermitian W and an orthogonal neutral projector Q,
the spectral defect is exactly the slack in the original
corner-neutral partial-isometry equations. -/
theorem sixMatrix_hermitian_zeroNeutral_blockDefect
    (W Q : SixMat)
    (hWW : W.IsHermitian)
    (hQ : Q * Q = Q)
    (hQQ : Q * W * Q = 0)
    (hQH : Q.IsHermitian) :
    let C : SixMat := 1 - Q
    let X : SixMat := C * W * C
    let Y : SixMat := C * W * Q
    let Δ : SixMat := 1 - W * W
    X * X + Y * Y.conjTranspose = C - C * Δ * C ∧
      X * Y = -(C * Δ * Q) ∧
      Y.conjTranspose * Y = Q - Q * Δ * Q := by
  let C : SixMat := 1 - Q
  let X : SixMat := C * W * C
  let Y : SixMat := C * W * Q
  let Z : SixMat := Q * W * C
  let Δ : SixMat := 1 - W * W
  change X * X + Y * Y.conjTranspose = C - C * Δ * C ∧
    X * Y = -(C * Δ * Q) ∧
    Y.conjTranspose * Y = Q - Q * Δ * Q
  obtain ⟨hXX, hXY, _, hZY⟩ :=
    sixMatrix_zeroNeutral_fullBlockDefect W Q hQ hQQ
  have hYStar : Y.conjTranspose = Z :=
    sixCornerToNeutralBlock_conjTranspose W Q hWW hQH
  exact ⟨by rw [hYStar]; exact hXX, hXY,
    by rw [hYStar]; exact hZY⟩

/-- The non-saturated defect equations hold in the genuine
six-dimensional positive signed Dirac chart, with arbitrary
truth-fibre multiplicities and no saturated-energy premises. -/
theorem sixLabelled_plusWitness_nonSaturated_blockDefect
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i)) :
    let W : SixMat := labelledSquareA label D + labelledSquareB label D
    let Q : SixMat := sixTruthSectorProjection label squarePlusNeutral
    let C : SixMat := 1 - Q
    let X : SixMat := C * W * C
    let Y : SixMat := C * W * Q
    let Δ : SixMat := 1 - W * W
    X * X + Y * Y.conjTranspose = C - C * Δ * C ∧
      X * Y = -(C * Δ * Q) ∧
      Y.conjTranspose * Y = Q - Q * Δ * Q := by
  dsimp only
  apply sixMatrix_hermitian_zeroNeutral_blockDefect
  · exact sixLabelled_plusWitness_isHermitian label D hD
  · exact sixTruthSectorProjection_idempotent label squarePlusNeutral
  · exact sixTruthSectorProjection_W_zero label squarePlusNeutral _
      (sixLabelled_plusWitness_neutral_entry_zero label D)
  · exact sixTruthSectorProjection_isHermitian label squarePlusNeutral

end Neoplatonic.LTR
