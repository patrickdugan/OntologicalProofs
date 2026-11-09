import Neoplatonic.LTR.FiveDimensionalOrthonormalExtension
import Mathlib.Tactic

/-!
# LTR-MAN-19: signed extremal unit eigenvectors form an orthonormal quartet

Given unit +1 and -1 eigenvectors of self-adjoint coordinate operators A and
B, the within-direction eigenvectors are orthogonal by self-adjointness.
The cross-direction vectors are orthogonal by MAN-13 and the parallelogram
contraction lemma. The four vectors are consequently orthonormal.

MAN-18 then extends them into the five-dimensional spectral matrix normal
form and proves both products vanish. This removes the supplied orthonormal
family from the MAN-18 premise.

Existence of the signed extremal unit eigenvectors from the spectral radius,
norm-one property, and grading symmetry remains a separate formal obligation.
-/

namespace Neoplatonic.LTR

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Distinct signed eigenvectors of a self-adjoint complex Hilbert operator
are orthogonal. -/
theorem selfAdjoint_oppositeSignedEigenvectors_orthogonal
    (T : E →L[ℂ] E) (hT : IsSelfAdjoint T)
    (x y : E) (hx : T x = x) (hy : T y = -y) :
    inner ℂ x y = 0 := by
  have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hT) x y
  have hx' : (T : E →ₗ[ℂ] E) x = x := hx
  have hy' : (T : E →ₗ[ℂ] E) y = -y := hy
  rw [hx', hy', inner_neg_right] at hs
  have hz : (2 : ℂ) * inner ℂ x y = 0 := by
    linear_combination hs
  exact (mul_eq_zero.mp hz).resolve_left (by norm_num)

/-- Four unit signed extremal eigenvectors of the two coordinate operators
give the five-dimensional zero-product obstruction.

Cross-direction orthogonality is derived from MAN-13, while within-direction
orthogonality follows from the self-adjoint operators' symmetry. -/
theorem fiveDim_signedUnitEigenvectors_zeroProducts
    (A B : E →L[ℂ] E)
    (hDim : Module.finrank ℂ E = 5)
    (hplus : ‖A + B‖ ≤ 1)
    (hminus : ‖A - B‖ ≤ 1)
    (hAself : IsSelfAdjoint A)
    (hBself : IsSelfAdjoint B)
    (htrA : LinearMap.trace ℂ E A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ E B.toLinearMap = 0)
    (u0 u1 u2 u3 : E)
    (hn0 : ‖u0‖ = 1) (hn1 : ‖u1‖ = 1)
    (hn2 : ‖u2‖ = 1) (hn3 : ‖u3‖ = 1)
    (hA0 : A u0 = u0) (hA1 : A u1 = -u1)
    (hB2 : B u2 = u2) (hB3 : B u3 = -u3) :
    A.toLinearMap * B.toLinearMap = 0 ∧
      B.toLinearMap * A.toLinearMap = 0 := by
  have h01 : inner ℂ u0 u1 = 0 :=
    selfAdjoint_oppositeSignedEigenvectors_orthogonal A hAself u0 u1 hA0 hA1
  have h23 : inner ℂ u2 u3 = 0 :=
    selfAdjoint_oppositeSignedEigenvectors_orthogonal B hBself u2 u3 hB2 hB3
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
  have h00 : inner ℂ u0 u0 = 1 := by simp [inner_self_eq_norm_sq_to_K, hn0]
  have h11 : inner ℂ u1 u1 = 1 := by simp [inner_self_eq_norm_sq_to_K, hn1]
  have h22 : inner ℂ u2 u2 = 1 := by simp [inner_self_eq_norm_sq_to_K, hn2]
  have h33 : inner ℂ u3 u3 = 1 := by simp [inner_self_eq_norm_sq_to_K, hn3]
  let v : Fin 5 → E :=
    fun i => if i = 0 then u0 else if i = 1 then u1
      else if i = 2 then u2 else if i = 3 then u3 else 0
  let s : Set (Fin 5) := {i | i < 4}
  have horth : Orthonormal ℂ (s.domRestrict v) := by
    classical
    rw [orthonormal_iff_ite]
    intro ⟨i,hi⟩ ⟨j,hj⟩
    change inner ℂ (v i) (v j) =
      (if (⟨i,hi⟩ : s) = ⟨j,hj⟩ then (1 : ℂ) else 0)
    change i < (4 : Fin 5) at hi
    change j < (4 : Fin 5) at hj
    fin_cases i <;> fin_cases j <;>
      simp_all [s, v, h00, h11, h22, h33,
        h01, h02, h03, h10, h12, h13, h20, h21, h23, h30, h31, h32]
  exact fiveDim_extremalOrthonormalFour_zeroProducts A B
    hDim hplus hminus hAself hBself htrA htrB v horth
    (by simpa [v] using hA0)
    (by simpa [v] using hA1)
    (by simpa [v] using hB2)
    (by simpa [v] using hB3)

end Neoplatonic.LTR
