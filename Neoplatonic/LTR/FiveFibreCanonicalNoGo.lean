import Neoplatonic.LTR.FiveFibreExactHammingAttainment
import Neoplatonic.LTR.FiveFibreCoordinateSpectralFacts
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic

/-!
# LTR-MAN-37: canonical five-dimensional exact Hamming no-go

The six exact Connes dual distances force the two Hermitian coordinate
commutators to have norm one and their sum and difference to be contractions
(MAN-27 through MAN-35).

The coordinate commutators, gradings, and trace identities are actual
five-by-five matrix expressions (MAN-36). Transport them through
Matrix.toEuclideanLin to continuous bounded operators on the genuine
five-dimensional complex Euclidean Hilbert space. MAN-21 then yields
both ordered operator products zero.

Transport their vanishing back to matrix products and invoke MAN-35's
isolated-fibre contradiction. This proves that no Hermitian Dirac matrix
on the canonical faithful (2,1,1,1) representation can realize all
six exact two-bit Hamming Connes distances.

The basis reduction of arbitrary faithful five-dimensional
representations to this canonical chart is a separate obligation.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev FiveFibreH := EuclideanSpace ℂ (Fin 5)
private abbrev FiveFibreMatrix := Matrix (Fin 5) (Fin 5) ℂ

/-- Transport matrix self-adjointness to the actual bounded
Hilbert operator on the canonical Euclidean space. -/
theorem fiveFibreSquare_matrixSelfAdjoint_toCLM
    (M : FiveFibreMatrix)
    (hM : IsSelfAdjoint M) :
    IsSelfAdjoint M.toEuclideanLin.toContinuousLinearMap := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr hM)

/-- The operator trace in the Euclidean chart is the matrix trace. -/
theorem fiveFibreSquare_trace_toEuclidean
    (M : FiveFibreMatrix) :
    LinearMap.trace ℂ FiveFibreH
      M.toEuclideanLin.toContinuousLinearMap.toLinearMap = M.trace := by
  change LinearMap.trace ℂ FiveFibreH M.toEuclideanLin = M.trace
  change LinearMap.trace ℂ FiveFibreH (Matrix.toLpLin 2 2 M) = M.trace
  rw [Matrix.toLpLin_eq_toLin]
  exact Matrix.trace_toLin_eq M (PiLp.basisFun (2 : ℝ≥0∞) ℂ (Fin 5))

/-- Multiplication of complex matrices agrees with composition of
their genuine Euclidean Hilbert linear maps. -/
theorem fiveFibreSquare_toEuclidean_mul
    (M N : FiveFibreMatrix) :
    (M * N).toEuclideanLin =
      M.toEuclideanLin.comp N.toEuclideanLin := by
  exact Matrix.toLpLin_mul_same (p := (2 : ℝ≥0∞)) M N

/-- The corresponding matrix-linear-map bridge transports zero
operator products back to zero matrix products. -/
theorem fiveFibreSquare_zeroMatrix_of_zeroEndomorphism
    (M N : FiveFibreMatrix)
    (h : (M.toEuclideanLin : FiveFibreH →ₗ[ℂ] FiveFibreH) *
      (N.toEuclideanLin : FiveFibreH →ₗ[ℂ] FiveFibreH) = 0) :
    M * N = 0 := by
  apply Matrix.toEuclideanLin.injective
  rw [fiveFibreSquare_toEuclidean_mul]
  simpa only [Module.End.mul_eq_comp, map_zero] using h

/-- In the canonical chart, the two actual Boolean Hermitian
coordinate commutators satisfy the five-dimensional zero-product
consequence of MAN-21 whenever their norms and their two opposite
witness contractions are unit-bounded. -/
theorem fiveFibreSquare_zeroProducts_of_spectralNorms
    (D : FiveFibreMatrix)
    (hD : ∀ i j, D i j = star (D j i))
    (hAnorm :
      ‖(fiveFibreSquareA D).toEuclideanLin.toContinuousLinearMap‖ = 1)
    (hBnorm :
      ‖(fiveFibreSquareB D).toEuclideanLin.toContinuousLinearMap‖ = 1)
    (hsum :
      ‖(fiveFibreSquareA D + fiveFibreSquareB D
         ).toEuclideanLin.toContinuousLinearMap‖ ≤ 1)
    (hdiff :
      ‖(fiveFibreSquareA D - fiveFibreSquareB D
         ).toEuclideanLin.toContinuousLinearMap‖ ≤ 1) :
    fiveFibreSquareA D * fiveFibreSquareB D = 0 ∧
      fiveFibreSquareB D * fiveFibreSquareA D = 0 := by
  let A : FiveFibreH →L[ℂ] FiveFibreH :=
    (fiveFibreSquareA D).toEuclideanLin.toContinuousLinearMap
  let B : FiveFibreH →L[ℂ] FiveFibreH :=
    (fiveFibreSquareB D).toEuclideanLin.toContinuousLinearMap
  let GA : FiveFibreH →ₗ[ℂ] FiveFibreH :=
    fiveFibreSquareGradeP.toEuclideanLin
  let GB : FiveFibreH →ₗ[ℂ] FiveFibreH :=
    fiveFibreSquareGradeQ.toEuclideanLin
  have hDim : Module.finrank ℂ FiveFibreH = 5 := by
    simp
  have hplus : ‖A + B‖ ≤ 1 := by
    have h : A + B =
        (fiveFibreSquareA D + fiveFibreSquareB D
          ).toEuclideanLin.toContinuousLinearMap := by
      ext v
      simp [A, B]
    rw [h]
    exact hsum
  have hminus : ‖A - B‖ ≤ 1 := by
    have h : A - B =
        (fiveFibreSquareA D - fiveFibreSquareB D
          ).toEuclideanLin.toContinuousLinearMap := by
      ext v
      simp [A, B]
    rw [h]
    exact hdiff
  have hAself : IsSelfAdjoint A :=
    fiveFibreSquare_matrixSelfAdjoint_toCLM _ (fiveFibreSquareA_selfAdjoint D hD)
  have hBself : IsSelfAdjoint B :=
    fiveFibreSquare_matrixSelfAdjoint_toCLM _ (fiveFibreSquareB_selfAdjoint D hD)
  have htrA : LinearMap.trace ℂ FiveFibreH A.toLinearMap = 0 := by
    change LinearMap.trace ℂ FiveFibreH
      (fiveFibreSquareA D).toEuclideanLin.toContinuousLinearMap.toLinearMap = 0
    rw [fiveFibreSquare_trace_toEuclidean]
    exact fiveFibreSquareA_trace_zero D
  have htrB : LinearMap.trace ℂ FiveFibreH B.toLinearMap = 0 := by
    change LinearMap.trace ℂ FiveFibreH
      (fiveFibreSquareB D).toEuclideanLin.toContinuousLinearMap.toLinearMap = 0
    rw [fiveFibreSquare_trace_toEuclidean]
    exact fiveFibreSquareB_trace_zero D
  have hGA : GA.comp GA = LinearMap.id := by
    have h := congrArg
      (fun M : FiveFibreMatrix => M.toEuclideanLin)
      fiveFibreSquareGradeP_square_one
    simpa [GA, fiveFibreSquare_toEuclidean_mul, Matrix.toLpLin_one] using h
  have hGB : GB.comp GB = LinearMap.id := by
    have h := congrArg
      (fun M : FiveFibreMatrix => M.toEuclideanLin)
      fiveFibreSquareGradeQ_square_one
    simpa [GB, fiveFibreSquare_toEuclidean_mul, Matrix.toLpLin_one] using h
  have hAG : A.toLinearMap.comp GA = -(GA.comp A.toLinearMap) := by
    have hm : fiveFibreSquareA D * fiveFibreSquareGradeP =
        -(fiveFibreSquareGradeP * fiveFibreSquareA D) := by
      rw [fiveFibreSquareGradeP_anticommutes]
      simp
    have h := congrArg (fun M : FiveFibreMatrix => M.toEuclideanLin) hm
    simpa [A, GA, fiveFibreSquare_toEuclidean_mul] using h
  have hBG : B.toLinearMap.comp GB = -(GB.comp B.toLinearMap) := by
    have hm : fiveFibreSquareB D * fiveFibreSquareGradeQ =
        -(fiveFibreSquareGradeQ * fiveFibreSquareB D) := by
      rw [fiveFibreSquareGradeQ_anticommutes]
      simp
    have h := congrArg (fun M : FiveFibreMatrix => M.toEuclideanLin) hm
    simpa [B, GB, fiveFibreSquare_toEuclidean_mul] using h
  obtain ⟨hab, hba⟩ := fiveDim_gradedCoordinates_zeroProducts
    A B GA GB hDim hplus hminus hAself hBself
    hAnorm hBnorm htrA htrB hGA hGB hAG hBG
  exact ⟨
    fiveFibreSquare_zeroMatrix_of_zeroEndomorphism
      (fiveFibreSquareA D) (fiveFibreSquareB D) hab,
    fiveFibreSquare_zeroMatrix_of_zeroEndomorphism
      (fiveFibreSquareB D) (fiveFibreSquareA D) hba⟩

/-- Exact Hamming Connes distances force a contradiction in the
canonical faithful five-dimensional representation (2,1,1,1).
All six distances are the actual extended-real dual suprema. -/
theorem fiveFibreSquare_exactHamming_canonical_noGo
    (D : FiveFibreMatrix)
    (hD : ∀ i j, D i j = star (D j i))
    (hd01 : fiveFibreSquareConnesDualDistance D 0 1 = 1)
    (hd02 : fiveFibreSquareConnesDualDistance D 0 2 = 1)
    (hd31 : fiveFibreSquareConnesDualDistance D 3 1 = 1)
    (hd32 : fiveFibreSquareConnesDualDistance D 3 2 = 1)
    (hd03 : fiveFibreSquareConnesDualDistance D 0 3 = 2)
    (hd12 : fiveFibreSquareConnesDualDistance D 1 2 = 2) :
    False := by
  obtain ⟨hAnorm, hBnorm⟩ :=
    fiveFibreSquare_exactHamming_normOne
      D hd01 hd02 hd31 hd32 hd03 hd12
  obtain ⟨hsum, hdiff⟩ :=
    fiveFibreSquare_exactHamming_force_witnesses
      D hd01 hd02 hd31 hd32 hd03 hd12
  obtain ⟨hp, hm⟩ :=
    fiveFibreSquare_oppositeWitnesses_contractions
      D (by simpa only [fiveFibreSquareDiracComm] using hsum)
        (by simpa only [fiveFibreSquareDiracComm] using hdiff)
  obtain ⟨hab, hba⟩ :=
    fiveFibreSquare_zeroProducts_of_spectralNorms
      D hD hAnorm hBnorm hp hm
  exact fiveFibreSquare_exactHamming_noGo_of_zeroProducts
    D hD hab hba hd01 hd02 hd31 hd32 hd03 hd12

end Neoplatonic.LTR
