import Neoplatonic.LTR.SixDimensionalSignedCornerTripotence
import Mathlib.Tactic

/-!
# LTR-MAN-94: exact corner-neutral block equations for an involutive witness

For an actual complex six-dimensional matrix W with W²=I, an
idempotent neutral-sector projection Q, and QWQ=0, define
C=I-Q, X=CWC, Y=CWQ, Z=QWC.

The four block equations hold as exact identities in the original
six-dimensional matrix ring:

    X² + YZ = C,    XY=0,    ZX=0,    ZY=Q.

With W and Q Hermitian, Z=Y.conjTranspose, so

    X² + YY.conjTranspose = C,   XY=0,   Y.conjTransposeY=Q.

This supplies the complementary partial-isometry equations underlying
the opposite-double rank problem. No coordinate pattern, rank
hypothesis or metric assumptions are needed for the algebraic lemmas.
-/

namespace Neoplatonic.LTR

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Corner-to-neutral part of an ambient matrix relative to an
orthogonal truth-sector projector. -/
def sixCornerToNeutralBlock (W Q : SixMat) : SixMat :=
  (1 - Q) * W * Q

/-- Neutral-to-corner part of an ambient matrix. -/
def sixNeutralToCornerBlock (W Q : SixMat) : SixMat :=
  Q * W * (1 - Q)

/-- The full set of exact complementary block equations, deduced
from a matrix involution with a zero neutral-neutral block. -/
theorem sixMatrix_involution_zeroNeutral_fullBlockEquations
    (W Q : SixMat)
    (hW : W * W = 1)
    (hQ : Q * Q = Q)
    (hQQ : Q * W * Q = 0) :
    let C : SixMat := 1 - Q
    let X : SixMat := C * W * C
    let Y : SixMat := C * W * Q
    let Z : SixMat := Q * W * C
    X * X + Y * Z = C ∧
      X * Y = 0 ∧ Z * X = 0 ∧ Z * Y = Q := by
  let C : SixMat := 1 - Q
  let X : SixMat := C * W * C
  let Y : SixMat := C * W * Q
  let Z : SixMat := Q * W * C
  change X * X + Y * Z = C ∧
    X * Y = 0 ∧ Z * X = 0 ∧ Z * Y = Q
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
  have hCW2C : C * W * W * C = C := by
    calc
      C * W * W * C = C * (W * W) * C := by noncomm_ring
      _ = C * 1 * C := by rw [hW]
      _ = C := by simpa using hCC
  have hCW2Q : C * W * W * Q = 0 := by
    calc
      C * W * W * Q = C * (W * W) * Q := by noncomm_ring
      _ = C * 1 * Q := by rw [hW]
      _ = 0 := by simpa using hCQ
  have hQW2C : Q * W * W * C = 0 := by
    calc
      Q * W * W * C = Q * (W * W) * C := by noncomm_ring
      _ = Q * 1 * C := by rw [hW]
      _ = 0 := by simpa using hQC
  have hQW2Q : Q * W * W * Q = Q := by
    calc
      Q * W * W * Q = Q * (W * W) * Q := by noncomm_ring
      _ = Q * 1 * Q := by rw [hW]
      _ = Q := by simpa using hQ
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
  have hXXYZ : X * X + Y * Z = C := by
    calc
      X * X + Y * Z = C * W * (C * C + Q * Q) * W * C := by
        dsimp [X, Y, Z]
        noncomm_ring
      _ = C * W * (C + Q) * W * C := by rw [hCC, hQ]
      _ = C * W * W * C := by rw [hCplus]; noncomm_ring
      _ = C := hCW2C
  have hXY : X * Y = 0 := by
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
      _ = 0 := by rw [hCW2Q, hCWQWQ]; simp
  have hZX : Z * X = 0 := by
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
      _ = 0 := by rw [hQW2C, hQWQWC]; simp
  have hZY : Z * Y = Q := by
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
      _ = Q := by rw [hQW2Q, hQWQWQ]; simp
  exact ⟨hXXYZ, hXY, hZX, hZY⟩

/-- For Hermitian W and Q, the neutral-to-corner block is
the conjugate transpose of the corner-to-neutral block. -/
theorem sixCornerToNeutralBlock_conjTranspose
    (W Q : SixMat) (hW : W.IsHermitian) (hQ : Q.IsHermitian) :
    (sixCornerToNeutralBlock W Q).conjTranspose =
      sixNeutralToCornerBlock W Q := by
  have hC : (1 - Q).conjTranspose = (1 - Q : SixMat) := by
    simp [Matrix.conjTranspose_sub, hQ.eq]
  unfold sixCornerToNeutralBlock sixNeutralToCornerBlock
  simp only [Matrix.conjTranspose_mul, hW.eq, hQ.eq, hC]
  noncomm_ring

/-- The Hermitian corner-neutral block equations become
X²+YY.conjTranspose=C, XY=0, and Y.conjTransposeY=Q, proving the neutral-to-corner
map is a partial isometry with initial projection Q. -/
theorem sixMatrix_hermitianInvolution_zeroNeutral_partialIsometry
    (W Q : SixMat)
    (hW : W * W = 1)
    (hWW : W.IsHermitian)
    (hQ : Q * Q = Q)
    (hQQ : Q * W * Q = 0)
    (hQH : Q.IsHermitian) :
    let C : SixMat := 1 - Q
    let X : SixMat := C * W * C
    let Y : SixMat := C * W * Q
    X * X + Y * Y.conjTranspose = C ∧ X * Y = 0 ∧ Y.conjTranspose * Y = Q := by
  let C : SixMat := 1 - Q
  let X : SixMat := C * W * C
  let Y : SixMat := C * W * Q
  let Z : SixMat := Q * W * C
  change X * X + Y * Y.conjTranspose = C ∧ X * Y = 0 ∧ Y.conjTranspose * Y = Q
  obtain ⟨hX, hXY, _, hZY⟩ :=
    sixMatrix_involution_zeroNeutral_fullBlockEquations W Q hW hQ hQQ
  have hYZ : Y.conjTranspose = Z :=
    sixCornerToNeutralBlock_conjTranspose W Q hWW hQH
  exact ⟨by rw [hYZ]; exact hX, hXY,
    by rw [hYZ]; exact hZY⟩

end Neoplatonic.LTR
