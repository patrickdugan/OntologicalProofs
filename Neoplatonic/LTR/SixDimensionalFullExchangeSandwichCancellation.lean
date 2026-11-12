import Neoplatonic.LTR.SixDimensionalOverneutralExchangeRank
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic

/-!
# LTR-MAN-186: cancel a full active-rank Hermitian exchange sandwich

For complex square 6×6 matrices C,Y, suppose CY=Y and
rank(Y)=rank(C). Then the column range of Y fills the range
of C. Elementary linear algebra produces an actual matrix R
with YR=C by choosing preimages of the six columns of C.

If C is Hermitian and X=CXC, the exact Gram sandwich
Yᴴ X Y=0 implies
  X=CXC=(YR)ᴴ X(YR)=Rᴴ(Yᴴ X Y)R=0.

This proof uses actual six-coordinate complex matrices and
the faithful finite-dimensional column-span rank, independent
of a canonical 2×2 unitary gauge or saturation.

MAN-184 supplies the sandwich for the cubic negative witness.
MAN-185 supplies rank(Y)=rank(C)=2 from the quartet.
Their combination removes the opposite 01↔10 Dirac block.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal ComplexOrder Matrix.Norms.L2Operator

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- If a matrix Y is supported on the output range of C and has
exactly the same rank, every column of C is in the range of Y.
This produces an explicit right matrix factor YR=C. -/
theorem sixMatrix_fullExchange_exists_rightFactor
    (C Y : SixMat)
    (hCY : C * Y = Y)
    (hRank : Y.rank = C.rank) :
    ∃ R : SixMat, Y * R = C := by
  classical
  have hCYfun (x : Fin 6 → ℂ) :
      C.mulVec (Y.mulVec x) = Y.mulVec x := by
    calc
      C.mulVec (Y.mulVec x) = (C * Y).mulVec x :=
        (Matrix.mulVec_mulVec C Y x).symm
      _ = Y.mulVec x := by rw [hCY]
  have hRangeLe :
      LinearMap.range Y.mulVecLin ≤ LinearMap.range C.mulVecLin := by
    intro z hz
    obtain ⟨x, rfl⟩ := hz
    exact ⟨Y.mulVec x, hCYfun x⟩
  have hFin :
      Module.finrank ℂ (LinearMap.range Y.mulVecLin) =
        Module.finrank ℂ (LinearMap.range C.mulVecLin) := hRank
  have hRangeEq :
      LinearMap.range Y.mulVecLin = LinearMap.range C.mulVecLin :=
    Submodule.eq_of_le_of_finrank_eq hRangeLe hFin
  have hPreimage (j : Fin 6) :
      ∃ x : Fin 6 → ℂ, Y.mulVec x = C.col j := by
    have hCmem : C.col j ∈ LinearMap.range C.mulVecLin := by
      refine ⟨Pi.single j (1 : ℂ), ?_⟩
      simpa only [Matrix.mulVecLin_apply] using
        (Matrix.mulVec_single_one C j)
    rw [← hRangeEq] at hCmem
    obtain ⟨x, hx⟩ := hCmem
    exact ⟨x, hx⟩
  choose x hx using hPreimage
  let R : SixMat := fun i j => x j i
  refine ⟨R, ?_⟩
  ext i j
  have h := congrArg (fun v : Fin 6 → ℂ => v i) (hx j)
  simpa [R, Matrix.mulVec, Matrix.mul_apply, Matrix.col_apply,
    dotProduct] using h

/-- A right factor of a Hermitian corner projection allows exact
cancellation of a full-rank neutral-exchange Gram sandwich. -/
theorem sixMatrix_rightFactor_sandwich_zero_forces_corner_zero
    (C X Y R : SixMat)
    (hCH : C.IsHermitian)
    (hX : C * X * C = X)
    (hYR : Y * R = C)
    (hSand : Y.conjTranspose * X * Y = 0) :
    X = 0 := by
  have hAdj : R.conjTranspose * Y.conjTranspose = C := by
    have h := congrArg Matrix.conjTranspose hYR
    simpa only [Matrix.conjTranspose_mul, hCH.eq] using h
  calc
    X = C * X * C := hX.symm
    _ = (R.conjTranspose * Y.conjTranspose) * X * (Y * R) := by
      rw [hAdj, hYR]
    _ = R.conjTranspose * (Y.conjTranspose * X * Y) * R := by
      noncomm_ring
    _ = 0 := by rw [hSand]; simp

/-- The active Hermitian 6D corner vanishes whenever a
neutral-to-active block fills the entire corner and its
sandwich Yᴴ X Y is zero. -/
theorem sixMatrix_fullRankExchange_sandwich_zero_forces_corner_zero
    (C X Y : SixMat)
    (hCH : C.IsHermitian)
    (hCY : C * Y = Y)
    (hX : C * X * C = X)
    (hRank : Y.rank = C.rank)
    (hSand : Y.conjTranspose * X * Y = 0) :
    X = 0 := by
  obtain ⟨R, hYR⟩ :=
    sixMatrix_fullExchange_exists_rightFactor C Y hCY hRank
  exact sixMatrix_rightFactor_sandwich_zero_forces_corner_zero
    C X Y R hCH hX hYR hSand

end Neoplatonic.LTR
