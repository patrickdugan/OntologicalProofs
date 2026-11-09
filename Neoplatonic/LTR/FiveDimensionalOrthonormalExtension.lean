import Neoplatonic.LTR.FiveDimensionalSpectralResidual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-!
# LTR-MAN-18: extend four extremal vectors into the 5D spectral certificate

This module transports MAN-17's concrete matrix zero-product theorem back to
real complex Hilbert-space operators. An orthonormal four-vector family
consisting of A's signed extremal eigenvectors and B's signed extremal
eigenvectors extends to a five-vector orthonormal basis.

MAN-13 supplies the cross-direction annihilation columns from the two
contraction hypotheses. In an orthonormal basis, self-adjointness gives
Hermitian matrices and the operator traces agree with matrix traces.
MAN-17 then proves both products vanish.

This theorem takes the four-vector orthonormal family as an explicit
hypothesis. Constructing that family from the norm-one, grading-involution,
and dimension hypotheses is the remaining spectral existence obligation.
-/

namespace Neoplatonic.LTR

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- Given four orthonormal signed extremal eigenvectors of two Hermitian
Hilbert-space coordinate operators, the two-direction contraction and
trace-zero hypotheses imply their products vanish in dimension five.

The orthonormality premise is on the first four elements of a Fin 5
family. The fifth basis vector is constructed by Mathlib's orthonormal
basis extension theorem. -/
theorem fiveDim_extremalOrthonormalFour_zeroProducts
    (A B : E →L[ℂ] E)
    (hDim : Module.finrank ℂ E = 5)
    (hplus : ‖A + B‖ ≤ 1)
    (hminus : ‖A - B‖ ≤ 1)
    (hAself : IsSelfAdjoint A)
    (hBself : IsSelfAdjoint B)
    (htrA : LinearMap.trace ℂ E A.toLinearMap = 0)
    (htrB : LinearMap.trace ℂ E B.toLinearMap = 0)
    (v : Fin 5 → E)
    (horth : Orthonormal ℂ
      (({i : Fin 5 | i < 4} : Set (Fin 5)).domRestrict v))
    (hvA0 : A (v 0) = v 0)
    (hvA1 : A (v 1) = -(v 1))
    (hvB2 : B (v 2) = v 2)
    (hvB3 : B (v 3) = -(v 3)) :
    A.toLinearMap * B.toLinearMap = 0 ∧
      B.toLinearMap * A.toLinearMap = 0 := by
  let s : Set (Fin 5) := {i | i < 4}
  have hcard : Module.finrank ℂ E = Fintype.card (Fin 5) := by
    simpa using hDim
  obtain ⟨b, hb⟩ :=
    horth.exists_orthonormalBasis_extension_of_card_eq hcard
  have hb0 : b 0 = v 0 := hb 0 (by norm_num [s])
  have hb1 : b 1 = v 1 := hb 1 (by norm_num [s])
  have hb2 : b 2 = v 2 := hb 2 (by norm_num [s])
  have hb3 : b 3 = v 3 := hb 3 (by norm_num [s])
  have ha0 : A (b 0) = b 0 := by simpa only [hb0] using hvA0
  have ha1 : A (b 1) = -(b 1) := by simpa only [hb1] using hvA1
  have hb2eig : B (b 2) = b 2 := by simpa only [hb2] using hvB2
  have hb3eig : B (b 3) = -(b 3) := by simpa only [hb3] using hvB3
  have ha2 : A (b 2) = 0 := by
    exact twoDirection_unitEigenvector_annihilates_first A B
      hplus hminus (1 : ℂ) (by norm_num) (b 2)
      (by simpa using hb2eig)
  have ha3 : A (b 3) = 0 := by
    exact twoDirection_unitEigenvector_annihilates_first A B
      hplus hminus (-1 : ℂ) (by norm_num) (b 3)
      (by simpa using hb3eig)
  have hb0zero : B (b 0) = 0 := by
    exact twoDirection_unitEigenvector_annihilates_second A B
      hplus hminus (1 : ℂ) (by norm_num) (b 0)
      (by simpa using ha0)
  have hb1zero : B (b 1) = 0 := by
    exact twoDirection_unitEigenvector_annihilates_second A B
      hplus hminus (-1 : ℂ) (by norm_num) (b 1)
      (by simpa using ha1)
  let a : E →ₗ[ℂ] E := A.toLinearMap
  let c : E →ₗ[ℂ] E := B.toLinearMap
  let MA : Matrix (Fin 5) (Fin 5) ℂ := LinearMap.toMatrixOrthonormal b a
  let MB : Matrix (Fin 5) (Fin 5) ℂ := LinearMap.toMatrixOrthonormal b c
  have hAadj : a.adjoint = a :=
    (ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff A).mpr hAself
  have hBadj : c.adjoint = c :=
    (ContinuousLinearMap.isSelfAdjoint_toLinearMap_iff B).mpr hBself
  have hMAHerm : Matrix.conjTranspose MA = MA := by
    change Matrix.conjTranspose (LinearMap.toMatrix b.toBasis b.toBasis a) =
      LinearMap.toMatrix b.toBasis b.toBasis a
    rw [← LinearMap.toMatrix_adjoint b b, hAadj]
  have hMBHerm : Matrix.conjTranspose MB = MB := by
    change Matrix.conjTranspose (LinearMap.toMatrix b.toBasis b.toBasis c) =
      LinearMap.toMatrix b.toBasis b.toBasis c
    rw [← LinearMap.toMatrix_adjoint b b, hBadj]
  have hMAstar (i j : Fin 5) : MA i j = star (MA j i) := by
    have h := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℂ => M i j)
      hMAHerm.symm
    simpa only [Matrix.conjTranspose_apply] using h
  have hMBstar (i j : Fin 5) : MB i j = star (MB j i) := by
    have h := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℂ => M i j)
      hMBHerm.symm
    simpa only [Matrix.conjTranspose_apply] using h
  have hpair (i j : Fin 5) :
      inner ℂ (b i) (b j) = if i = j then 1 else 0 :=
    (orthonormal_iff_ite.mp b.orthonormal) i j
  have hMA0 (i : Fin 5) : MA i 0 = if i = 0 then 1 else 0 := by
    change LinearMap.toMatrixOrthonormal b a i 0 = _
    rw [LinearMap.toMatrixOrthonormal_apply_apply]
    change inner ℂ (b i) (A (b 0)) = _
    rw [ha0, hpair i 0]
  have hMA1 (i : Fin 5) : MA i 1 = if i = 1 then -1 else 0 := by
    change LinearMap.toMatrixOrthonormal b a i 1 = _
    rw [LinearMap.toMatrixOrthonormal_apply_apply]
    change inner ℂ (b i) (A (b 1)) = _
    rw [ha1, inner_neg_right, hpair i 1]
    by_cases h : i = 1 <;> simp [h]
  have hMA2 (i : Fin 5) : MA i 2 = 0 := by
    change LinearMap.toMatrixOrthonormal b a i 2 = _
    rw [LinearMap.toMatrixOrthonormal_apply_apply]
    change inner ℂ (b i) (A (b 2)) = 0
    simp [ha2]
  have hMA3 (i : Fin 5) : MA i 3 = 0 := by
    change LinearMap.toMatrixOrthonormal b a i 3 = _
    rw [LinearMap.toMatrixOrthonormal_apply_apply]
    change inner ℂ (b i) (A (b 3)) = 0
    simp [ha3]
  have hMB0 (i : Fin 5) : MB i 0 = 0 := by
    change LinearMap.toMatrixOrthonormal b c i 0 = _
    rw [LinearMap.toMatrixOrthonormal_apply_apply]
    change inner ℂ (b i) (B (b 0)) = 0
    simp [hb0zero]
  have hMB1 (i : Fin 5) : MB i 1 = 0 := by
    change LinearMap.toMatrixOrthonormal b c i 1 = _
    rw [LinearMap.toMatrixOrthonormal_apply_apply]
    change inner ℂ (b i) (B (b 1)) = 0
    simp [hb1zero]
  have hMB2 (i : Fin 5) : MB i 2 = if i = 2 then 1 else 0 := by
    change LinearMap.toMatrixOrthonormal b c i 2 = _
    rw [LinearMap.toMatrixOrthonormal_apply_apply]
    change inner ℂ (b i) (B (b 2)) = _
    rw [hb2eig, hpair i 2]
  have hMB3 (i : Fin 5) : MB i 3 = if i = 3 then -1 else 0 := by
    change LinearMap.toMatrixOrthonormal b c i 3 = _
    rw [LinearMap.toMatrixOrthonormal_apply_apply]
    change inner ℂ (b i) (B (b 3)) = _
    rw [hb3eig, inner_neg_right, hpair i 3]
    by_cases h : i = 3 <;> simp [h]
  have htrMA : MA.trace = 0 := by
    calc
      MA.trace = LinearMap.trace ℂ E a :=
        (LinearMap.trace_eq_matrix_trace ℂ b.toBasis a).symm
      _ = 0 := htrA
  have htrMB : MB.trace = 0 := by
    calc
      MB.trace = LinearMap.trace ℂ E c :=
        (LinearMap.trace_eq_matrix_trace ℂ b.toBasis c).symm
      _ = 0 := htrB
  have hZero := fiveDim_jointExtremalEigenbasis_zeroProducts MA MB
    hMAstar hMBstar hMA0 hMA1 hMA2 hMA3 hMB0 hMB1 hMB2 hMB3
    htrMA htrMB
  constructor
  · apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
    simpa only [LinearMap.toMatrix_mul, map_zero, MA, MB, a, c] using hZero.1
  · apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
    simpa only [LinearMap.toMatrix_mul, map_zero, MA, MB, a, c] using hZero.2

end Neoplatonic.LTR
