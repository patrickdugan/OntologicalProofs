import Neoplatonic.LTR.FiveFibreAtomicBasisLabels
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Tactic

/-!
# LTR-MAN-50: a common atomic eigenbasis gives a unitary matrix

The canonical Hilbert-coordinate basis and the subordinate orthonormal
basis from MAN-48 determine an actual five-by-five unitary matrix.
Its columns are exactly the common eigenvectors of the four atomic
truth projections, and its inverse sends each such eigenvector back
to the corresponding standard coordinate vector.

This turns the simultaneous eigenbasis construction into an explicit
unitary change of basis suitable for conjugating all four projectors.
-/

namespace Neoplatonic.LTR

private abbrev FiveAtomicH := EuclideanSpace ℂ (Fin 5)
private abbrev FiveAtomicMat := Matrix (Fin 5) (Fin 5) ℂ

/-- A unitary matrix whose columns form the common orthonormal basis
of all four truth projections. -/
noncomputable def FiveFibreAtomicResolution.atomicBasisUnitary
    (P : FiveFibreAtomicResolution) : Matrix.unitaryGroup (Fin 5) ℂ :=
  ⟨(EuclideanSpace.basisFun (Fin 5) ℂ).toBasis.toMatrix
      (P.atomicOrthonormalBasis).toBasis,
    (EuclideanSpace.basisFun (Fin 5) ℂ).toMatrix_orthonormalBasis_mem_unitary
      P.atomicOrthonormalBasis⟩

/-- The jth unitary column is the jth common atomic eigenvector. -/
@[simp] theorem FiveFibreAtomicResolution.atomicBasisUnitary_apply
    (P : FiveFibreAtomicResolution) (i j : Fin 5) :
    (P.atomicBasisUnitary : FiveAtomicMat) i j =
      ⇑(P.atomicOrthonormalBasis j) i := rfl

/-- Taking the jth column of the change-of-basis matrix recovers
the jth common atomic eigenvector. -/
@[simp] theorem FiveFibreAtomicResolution.atomicBasisUnitary_col
    (P : FiveFibreAtomicResolution) (j : Fin 5) :
    Matrix.col (P.atomicBasisUnitary : FiveAtomicMat) j =
      ⇑(P.atomicOrthonormalBasis j) := rfl

/-- Multiplying the jth coordinate unit vector by the unitary
recovers the common orthonormal basis vector at j. -/
theorem FiveFibreAtomicResolution.atomicBasisUnitary_mulVec
    (P : FiveFibreAtomicResolution) (j : Fin 5) :
    (P.atomicBasisUnitary : FiveAtomicMat) *ᵥ Pi.single j 1 =
      ⇑(P.atomicOrthonormalBasis j) := by
  simp_rw [Matrix.mulVec_single_one, P.atomicBasisUnitary_col]

/-- The inverse unitary takes the jth atomic eigenvector back to
the jth standard Hilbert-coordinate basis vector. -/
theorem FiveFibreAtomicResolution.atomicBasisUnitary_star_mulVec
    (P : FiveFibreAtomicResolution) (j : Fin 5) :
    (star (P.atomicBasisUnitary : FiveAtomicMat)) *ᵥ
      ⇑(P.atomicOrthonormalBasis j) = Pi.single j 1 := by
  rw [← P.atomicBasisUnitary_mulVec j, Matrix.mulVec_mulVec,
    Unitary.coe_star_mul_self, Matrix.one_mulVec]

/-- In the common unitary basis, the jth vector is a simultaneous
eigenvector for each truth projection, with indicator eigenvalue. -/
theorem FiveFibreAtomicResolution.atomicBasis_mulVec_eigen
    (P : FiveFibreAtomicResolution)
    (v : Fin 4) (j : Fin 5) :
    P.proj v *ᵥ ⇑(P.atomicOrthonormalBasis j) =
      (if v = P.atomicBasisLabel j then (1 : ℂ) else 0) •
        ⇑(P.atomicOrthonormalBasis j) := by
  have h := congrArg
    (fun x : FiveAtomicH => (⇑x : Fin 5 → ℂ))
    (P.atomicBasis_eigen v j)
  by_cases hv : v = P.atomicBasisLabel j
  · simpa [hv, Matrix.toLpLin_apply] using h
  · simpa [hv, Matrix.toLpLin_apply] using h

end Neoplatonic.LTR
