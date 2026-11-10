import Neoplatonic.LTR.TwoDirectionResidualReduction
import Mathlib.Tactic

/-!
# LTR-MAN-58: construct the four-dimensional extremal spectral sector

MAN-56 computes residual dimensions from an orthonormal quartet and
establishes invariance for the signed eigenvector residual.

Under the genuine two-coordinate hypotheses of the Hamming witness
argument, the graded norm-one theorem supplies both signed extremal
eigenvectors for each of A and B. The contraction and self-adjointness
theorems make all four mutually orthogonal. This constructs the
quartet with no assumed eigenvectors or orthonormal family.

Consequently the residual dimension two in ambient dimension six,
and dimension three in dimension seven, follow from the original
graded norm constraints with no supplied basis.
-/

namespace Neoplatonic.LTR

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Norm-one, graded, trace-free Hamming coordinate operators
admit an actual orthonormal quartet of signed extremal eigenvectors. -/
theorem twoDirection_gradedCoordinates_exists_orthonormalQuartet
    (A B : E →L[ℂ] E) (GA GB : E →ₗ[ℂ] E)
    (hplus : ‖A + B‖ ≤ 1)
    (hminus : ‖A - B‖ ≤ 1)
    (hAself : IsSelfAdjoint A)
    (hBself : IsSelfAdjoint B)
    (hAnorm : ‖A‖ = 1) (hBnorm : ‖B‖ = 1)
    (hGA : GA.comp GA = LinearMap.id)
    (hGB : GB.comp GB = LinearMap.id)
    (hAG : A.toLinearMap.comp GA = -(GA.comp A.toLinearMap))
    (hBG : B.toLinearMap.comp GB = -(GB.comp B.toLinearMap)) :
    ∃ q : Fin 4 → E,
      Orthonormal ℂ q ∧
      A (q 0) = q 0 ∧ A (q 1) = -(q 1) ∧
      B (q 2) = q 2 ∧ B (q 3) = -(q 3) := by
  obtain ⟨u0, u1, hn0, hn1, hA0, hA1⟩ :=
    gradedNormOne_exists_signedUnitEigenvectors
      A GA hAself hAnorm hGA hAG
  obtain ⟨u2, u3, hn2, hn3, hB2, hB3⟩ :=
    gradedNormOne_exists_signedUnitEigenvectors
      B GB hBself hBnorm hGB hBG
  have h01 : inner ℂ u0 u1 = 0 :=
    selfAdjoint_oppositeSignedEigenvectors_orthogonal
      A hAself u0 u1 hA0 hA1
  have h23 : inner ℂ u2 u3 = 0 :=
    selfAdjoint_oppositeSignedEigenvectors_orthogonal
      B hBself u2 u3 hB2 hB3
  have h02 : inner ℂ u0 u2 = 0 :=
    twoDirection_extremalEigenvectors_orthogonal A B hplus hminus
      hBself 1 1 (by norm_num) (by norm_num) u0 u2
      (by simpa using hA0) (by simpa using hB2)
  have h03 : inner ℂ u0 u3 = 0 :=
    twoDirection_extremalEigenvectors_orthogonal A B hplus hminus
      hBself 1 (-1) (by norm_num) (by norm_num) u0 u3
      (by simpa using hA0) (by simpa using hB3)
  have h12 : inner ℂ u1 u2 = 0 :=
    twoDirection_extremalEigenvectors_orthogonal A B hplus hminus
      hBself (-1) 1 (by norm_num) (by norm_num) u1 u2
      (by simpa using hA1) (by simpa using hB2)
  have h13 : inner ℂ u1 u3 = 0 :=
    twoDirection_extremalEigenvectors_orthogonal A B hplus hminus
      hBself (-1) (-1) (by norm_num) (by norm_num) u1 u3
      (by simpa using hA1) (by simpa using hB3)
  have flipZero (x y : E) (hxy : inner ℂ x y = 0) :
      inner ℂ y x = 0 := by
    have h : (starRingEnd ℂ) (inner ℂ y x) = 0 := by
      simpa only [hxy] using (inner_conj_symm (𝕜 := ℂ) x y)
    simpa using congrArg (starRingEnd ℂ) h
  have h10 : inner ℂ u1 u0 = 0 := flipZero u0 u1 h01
  have h20 : inner ℂ u2 u0 = 0 := flipZero u0 u2 h02
  have h30 : inner ℂ u3 u0 = 0 := flipZero u0 u3 h03
  have h21 : inner ℂ u2 u1 = 0 := flipZero u1 u2 h12
  have h31 : inner ℂ u3 u1 = 0 := flipZero u1 u3 h13
  have h32 : inner ℂ u3 u2 = 0 := flipZero u2 u3 h23
  have h00 : inner ℂ u0 u0 = 1 := by
    simp [inner_self_eq_norm_sq_to_K, hn0]
  have h11 : inner ℂ u1 u1 = 1 := by
    simp [inner_self_eq_norm_sq_to_K, hn1]
  have h22 : inner ℂ u2 u2 = 1 := by
    simp [inner_self_eq_norm_sq_to_K, hn2]
  have h33 : inner ℂ u3 u3 = 1 := by
    simp [inner_self_eq_norm_sq_to_K, hn3]
  let q : Fin 4 → E :=
    fun i => if i = 0 then u0 else if i = 1 then u1
      else if i = 2 then u2 else u3
  have horth : Orthonormal ℂ q := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp_all [q]
  refine ⟨q, horth, ?_, ?_, ?_, ?_⟩
  · simpa [q] using hA0
  · simpa [q] using hA1
  · simpa [q] using hB2
  · simpa [q] using hB3

/-- Every actual six-dimensional graded norm-one Hamming coordinate
pair has a two-dimensional common residual complement. -/
theorem twoDirection_sixDim_graded_exists_residual2
    (A B : E →L[ℂ] E) (GA GB : E →ₗ[ℂ] E)
    (hDim : Module.finrank ℂ E = 6)
    (hplus : ‖A + B‖ ≤ 1) (hminus : ‖A - B‖ ≤ 1)
    (hAself : IsSelfAdjoint A) (hBself : IsSelfAdjoint B)
    (hAnorm : ‖A‖ = 1) (hBnorm : ‖B‖ = 1)
    (hGA : GA.comp GA = LinearMap.id)
    (hGB : GB.comp GB = LinearMap.id)
    (hAG : A.toLinearMap.comp GA = -(GA.comp A.toLinearMap))
    (hBG : B.toLinearMap.comp GB = -(GB.comp B.toLinearMap)) :
    ∃ q : Fin 4 → E, Orthonormal ℂ q ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range q))ᗮ = 2 := by
  obtain ⟨q, hq, _, _, _, _⟩ :=
    twoDirection_gradedCoordinates_exists_orthonormalQuartet
      A B GA GB hplus hminus hAself hBself
      hAnorm hBnorm hGA hGB hAG hBG
  exact ⟨q, hq, twoDirection_sixDim_residual_finrank q hq hDim⟩

/-- Every actual seven-dimensional graded norm-one Hamming coordinate
pair has a three-dimensional common residual complement. -/
theorem twoDirection_sevenDim_graded_exists_residual3
    (A B : E →L[ℂ] E) (GA GB : E →ₗ[ℂ] E)
    (hDim : Module.finrank ℂ E = 7)
    (hplus : ‖A + B‖ ≤ 1) (hminus : ‖A - B‖ ≤ 1)
    (hAself : IsSelfAdjoint A) (hBself : IsSelfAdjoint B)
    (hAnorm : ‖A‖ = 1) (hBnorm : ‖B‖ = 1)
    (hGA : GA.comp GA = LinearMap.id)
    (hGB : GB.comp GB = LinearMap.id)
    (hAG : A.toLinearMap.comp GA = -(GA.comp A.toLinearMap))
    (hBG : B.toLinearMap.comp GB = -(GB.comp B.toLinearMap)) :
    ∃ q : Fin 4 → E, Orthonormal ℂ q ∧
      Module.finrank ℂ (Submodule.span ℂ (Set.range q))ᗮ = 3 := by
  obtain ⟨q, hq, _, _, _, _⟩ :=
    twoDirection_gradedCoordinates_exists_orthonormalQuartet
      A B GA GB hplus hminus hAself hBself
      hAnorm hBnorm hGA hGB hAG hBG
  exact ⟨q, hq, twoDirection_sevenDim_residual_finrank q hq hDim⟩

end Neoplatonic.LTR
