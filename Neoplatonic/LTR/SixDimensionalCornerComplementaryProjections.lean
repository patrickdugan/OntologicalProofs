import Neoplatonic.LTR.SixDimensionalCornerSpectralRank
import Mathlib.Tactic

/-!
# LTR-MAN-97: complementary corner projections without spectral assumptions

For a six-dimensional involution W with a zero neutral-neutral block
QWQ=0, decompose it over C=I-Q as

  X = CWC,  Y = CWQ,  Z = QWC.

MAN-94 established X²+YZ=C, XY=0, ZX=0 and ZY=Q.

The two corner terms X² and YZ are complementary idempotents,
which mutually annihilate, without Hermitianity. When Q has trace
two, each has rank exactly two. For Hermitian W,Q the second
projection is the orthogonal projection YYᴴ onto the isometric
image of the two-dimensional neutral truth sector.

The rank statement applies in the original six-dimensional coordinate
chart, with arbitrary repeated truth labels.
-/

namespace Neoplatonic.LTR

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The spectral corner square and the neutral-exchange corner
product are exact complementary idempotents even before
Hermitianity is imposed. -/
theorem sixMatrix_involution_zeroNeutral_complementaryCornerProjections
    (W Q : SixMat)
    (hW : W * W = 1)
    (hQ : Q * Q = Q)
    (hQQ : Q * W * Q = 0) :
    let C : SixMat := 1 - Q
    let X : SixMat := C * W * C
    let Y : SixMat := C * W * Q
    let Z : SixMat := Q * W * C
    (X * X) * (X * X) = X * X ∧
      (Y * Z) * (Y * Z) = Y * Z ∧
      (X * X) * (Y * Z) = 0 ∧
      (Y * Z) * (X * X) = 0 ∧
      X * X + Y * Z = C := by
  let C : SixMat := 1 - Q
  let X : SixMat := C * W * C
  let Y : SixMat := C * W * Q
  let Z : SixMat := Q * W * C
  change (X * X) * (X * X) = X * X ∧
      (Y * Z) * (Y * Z) = Y * Z ∧
      (X * X) * (Y * Z) = 0 ∧
      (Y * Z) * (X * X) = 0 ∧ X * X + Y * Z = C
  obtain ⟨hSquare, hXY, hZX, hZY⟩ :=
    sixMatrix_involution_zeroNeutral_fullBlockEquations W Q hW hQ hQQ
  have hYQ : Y * Q = Y := by
    calc
      Y * Q = C * W * (Q * Q) := by dsimp [Y]; noncomm_ring
      _ = C * W * Q := by rw [hQ]
      _ = Y := rfl
  have hTrip : X * X * X = X := by
    exact sixMatrix_involution_zeroNeutral_corner_tripotent
      W Q hW hQ hQQ
  refine ⟨sixMatrix_tripotent_square_idempotent X hTrip, ?_, ?_, ?_, hSquare⟩
  · calc
      (Y * Z) * (Y * Z) = Y * (Z * Y) * Z := by noncomm_ring
      _ = Y * Q * Z := by rw [hZY]
      _ = Y * Z := by rw [hYQ]
  · calc
      (X * X) * (Y * Z) = (X * (X * Y)) * Z := by noncomm_ring
      _ = 0 := by rw [hXY]; simp
  · calc
      (Y * Z) * (X * X) = Y * (Z * X) * X := by noncomm_ring
      _ = 0 := by rw [hZX]; simp

/-- At neutral trace two, each of the two complementary
corner idempotents has exact rank two. This records both ranks,
rather than just the MAN-94 rank of X². -/
theorem sixMatrix_involution_neutralTraceTwo_bothCornerRanksTwo
    (W Q : SixMat)
    (hW : W * W = 1)
    (hQ : Q * Q = Q)
    (hQQ : Q * W * Q = 0)
    (hTrace : Q.trace = (2 : ℂ)) :
    let C : SixMat := 1 - Q
    let X : SixMat := C * W * C
    let Y : SixMat := C * W * Q
    let Z : SixMat := Q * W * C
    (X * X).rank = 2 ∧
      (Y * Z).rank = 2 := by
  let C : SixMat := 1 - Q
  let X : SixMat := C * W * C
  let Y : SixMat := C * W * Q
  let Z : SixMat := Q * W * C
  change (X * X).rank = 2 ∧ (Y * Z).rank = 2
  have hXrank :=
    (sixMatrix_involution_neutralTraceTwo_cornerRankTwo
      W Q hW hQ hQQ hTrace).2
  change (X * X).rank = 2 at hXrank
  have hYid :=
    (sixMatrix_involution_zeroNeutral_complementaryCornerProjections
      W Q hW hQ hQQ).2.1
  change (Y * Z) * (Y * Z) = Y * Z at hYid
  have hZY :=
    (sixMatrix_involution_zeroNeutral_fullBlockEquations
      W Q hW hQ hQQ).2.2.2
  change Z * Y = Q at hZY
  have hPtrace : (Y * Z).trace = (2 : ℂ) := by
    rw [Matrix.trace_mul_comm, hZY, hTrace]
  have hPrank : (Y * Z).rank = 2 := by
    have ht := sixMatrix_idempotent_trace_eq_rank (Y * Z) hYid
    rw [hPtrace] at ht
    exact_mod_cast ht.symm
  exact ⟨hXrank, hPrank⟩

/-- A Hermitian involution exchanges the neutral sector with
an orthogonal two-dimensional corner subspace; X² projects
onto the orthogonal complementary corner subspace. -/
theorem sixMatrix_hermitianInvolution_zeroNeutral_orthogonalCornerSplit
    (W Q : SixMat)
    (hW : W * W = 1)
    (hWH : W.IsHermitian)
    (hQ : Q * Q = Q)
    (hQQ : Q * W * Q = 0)
    (hQH : Q.IsHermitian)
    (hTrace : Q.trace = (2 : ℂ)) :
    let C : SixMat := 1 - Q
    let X : SixMat := C * W * C
    let Y : SixMat := C * W * Q
    (X * X) * (X * X) = X * X ∧
      (Y * Y.conjTranspose) * (Y * Y.conjTranspose) =
        Y * Y.conjTranspose ∧
      (X * X) * (Y * Y.conjTranspose) = 0 ∧
      (Y * Y.conjTranspose) * (X * X) = 0 ∧
      X * X + Y * Y.conjTranspose = C ∧
      (X * X).rank = 2 ∧
      (Y * Y.conjTranspose).rank = 2 := by
  let C : SixMat := 1 - Q
  let X : SixMat := C * W * C
  let Y : SixMat := C * W * Q
  let Z : SixMat := Q * W * C
  change (X * X) * (X * X) = X * X ∧
      (Y * Y.conjTranspose) * (Y * Y.conjTranspose) =
        Y * Y.conjTranspose ∧
      (X * X) * (Y * Y.conjTranspose) = 0 ∧
      (Y * Y.conjTranspose) * (X * X) = 0 ∧
      X * X + Y * Y.conjTranspose = C ∧
      (X * X).rank = 2 ∧
      (Y * Y.conjTranspose).rank = 2
  have hZ : Y.conjTranspose = Z := by
    exact sixCornerToNeutralBlock_conjTranspose W Q hWH hQH
  have hSplit := sixMatrix_involution_zeroNeutral_complementaryCornerProjections
    W Q hW hQ hQQ
  change (X * X) * (X * X) = X * X ∧
      (Y * Z) * (Y * Z) = Y * Z ∧
      (X * X) * (Y * Z) = 0 ∧
      (Y * Z) * (X * X) = 0 ∧
      X * X + Y * Z = C at hSplit
  have hRanks :=
    sixMatrix_involution_neutralTraceTwo_bothCornerRanksTwo
      W Q hW hQ hQQ hTrace
  change (X * X).rank = 2 ∧ (Y * Z).rank = 2 at hRanks
  rw [hZ]
  exact ⟨hSplit.1, hSplit.2.1, hSplit.2.2.1,
    hSplit.2.2.2.1, hSplit.2.2.2.2,
    hRanks.1, hRanks.2⟩

end Neoplatonic.LTR
