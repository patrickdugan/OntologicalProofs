import Neoplatonic.LTR.TwoDirectionContractions
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# LTR-MAN-13: mutual orthogonality of saturated Dirac directions

The MAN-12 parallelogram certificate says that if A+B and A-B are
contractions on a complex Hilbert space, a vector on which A preserves
norm is annihilated by B. The same holds with A and B interchanged.

An eigenvector with an eigenvalue of modulus one saturates this norm
bound. Accordingly the entire unit-circle eigenspace of A lies in
ker B, and conversely.

If B is self-adjoint, each nonzero B-eigenvector is orthogonal to
ker B. Combining this observation with the contraction certificate
shows that saturated A-eigenvectors and nonzero B-eigenvectors are
orthogonal.

For the two-bit Hamming obstruction, both self-adjoint coordinate
commutators have +1 and -1 extremal eigenvalues. The four pairwise
cross-direction orthogonality relations are special cases of the
general theorem proved here.

The existence and dimensions of these eigenspaces, and the
five-dimensional trace argument, are subsequent obligations.
-/

namespace Neoplatonic.LTR

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Every eigenvector of A at a unit-modulus scalar is annihilated
by B when the sum and difference are contractions. -/
theorem twoDirection_unitEigenvector_annihilates_second
    (A B : E →L[ℂ] E)
    (hplus : ‖A + B‖ ≤ 1)
    (hminus : ‖A - B‖ ≤ 1)
    (a : ℂ) (ha : ‖a‖ = 1)
    (v : E) (hv : A v = a • v) :
    B v = 0 := by
  have hnorm : ‖A v‖ = ‖v‖ := by
    rw [hv, norm_smul, ha, one_mul]
  exact twoDirection_first_saturating_annihilates_second
    A B hplus hminus v hnorm

/-- The symmetric statement: a B-eigenvector at a unit-modulus
eigenvalue is in the kernel of A. -/
theorem twoDirection_unitEigenvector_annihilates_first
    (A B : E →L[ℂ] E)
    (hplus : ‖A + B‖ ≤ 1)
    (hminus : ‖A - B‖ ≤ 1)
    (b : ℂ) (hb : ‖b‖ = 1)
    (w : E) (hw : B w = b • w) :
    A w = 0 := by
  have hnorm : ‖B w‖ = ‖w‖ := by
    rw [hw, norm_smul, hb, one_mul]
  exact twoDirection_second_saturating_annihilates_first
    A B hplus hminus w hnorm

/-- The entire unit-circle eigenspace of A lies in the kernel of B.
All spaces are actual linear submodules, including the zero vector. -/
theorem twoDirection_unitEigenspace_le_ker_second
    (A B : E →L[ℂ] E)
    (hplus : ‖A + B‖ ≤ 1)
    (hminus : ‖A - B‖ ≤ 1)
    (a : ℂ) (ha : ‖a‖ = 1) :
    Module.End.eigenspace (A : E →ₗ[ℂ] E) a ≤
      LinearMap.ker (B : E →ₗ[ℂ] E) := by
  intro v hv
  apply LinearMap.mem_ker.mpr
  exact twoDirection_unitEigenvector_annihilates_second
    A B hplus hminus a ha v
    (Module.End.mem_eigenspace_iff.mp hv)

/-- The symmetric eigenspace-to-kernel inclusion. -/
theorem twoDirection_unitEigenspace_le_ker_first
    (A B : E →L[ℂ] E)
    (hplus : ‖A + B‖ ≤ 1)
    (hminus : ‖A - B‖ ≤ 1)
    (b : ℂ) (hb : ‖b‖ = 1) :
    Module.End.eigenspace (B : E →ₗ[ℂ] E) b ≤
      LinearMap.ker (A : E →ₗ[ℂ] E) := by
  intro w hw
  apply LinearMap.mem_ker.mpr
  exact twoDirection_unitEigenvector_annihilates_first
    A B hplus hminus b hb w
    (Module.End.mem_eigenspace_iff.mp hw)

/-- For self-adjoint B, an A-eigenvector at any unit-modulus
eigenvalue is orthogonal to a B-eigenvector at any nonzero
eigenvalue. The proof uses the actual complex Hilbert inner product. -/
theorem twoDirection_extremalEigenvectors_orthogonal
    [CompleteSpace E]
    (A B : E →L[ℂ] E)
    (hplus : ‖A + B‖ ≤ 1)
    (hminus : ‖A - B‖ ≤ 1)
    (hB : IsSelfAdjoint B)
    (a b : ℂ) (ha : ‖a‖ = 1) (hb : b ≠ 0)
    (v w : E) (hv : A v = a • v) (hw : B w = b • w) :
    inner ℂ v w = 0 := by
  have hBv : B v = 0 :=
    twoDirection_unitEigenvector_annihilates_second A B
      hplus hminus a ha v hv
  have hsym : inner ℂ (B v) w = inner ℂ v (B w) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hB) v w
  rw [hBv, hw, inner_zero_left, inner_smul_right] at hsym
  exact (mul_eq_zero.mp hsym.symm).resolve_left hb

/-- Full eigenspaces, at every saturated A-eigenvalue and nonzero
B-eigenvalue, are pairwise orthogonal. -/
theorem twoDirection_extremalEigenspaces_orthogonal
    [CompleteSpace E]
    (A B : E →L[ℂ] E)
    (hplus : ‖A + B‖ ≤ 1)
    (hminus : ‖A - B‖ ≤ 1)
    (hB : IsSelfAdjoint B)
    (a b : ℂ) (ha : ‖a‖ = 1) (hb : b ≠ 0)
    (v w : E)
    (hv : v ∈ Module.End.eigenspace (A : E →ₗ[ℂ] E) a)
    (hw : w ∈ Module.End.eigenspace (B : E →ₗ[ℂ] E) b) :
    inner ℂ v w = 0 := by
  exact twoDirection_extremalEigenvectors_orthogonal A B
    hplus hminus hB a b ha hb v w
    (Module.End.mem_eigenspace_iff.mp hv)
    (Module.End.mem_eigenspace_iff.mp hw)

/-- Both signs of the extremal A-eigenvalues belong to the
kernel of B, as a single submodule inclusion. -/
theorem twoDirection_signedExtremalEigenspaces_le_ker
    (A B : E →L[ℂ] E)
    (hplus : ‖A + B‖ ≤ 1)
    (hminus : ‖A - B‖ ≤ 1) :
    (Module.End.eigenspace (A : E →ₗ[ℂ] E) 1 ⊔
      Module.End.eigenspace (A : E →ₗ[ℂ] E) (-1)) ≤
      LinearMap.ker (B : E →ₗ[ℂ] E) := by
  apply sup_le
  · exact twoDirection_unitEigenspace_le_ker_second
      A B hplus hminus 1 (by norm_num)
  · exact twoDirection_unitEigenspace_le_ker_second
      A B hplus hminus (-1) (by norm_num)

/-- The same signed-eigenspace inclusion with A and B reversed. -/
theorem twoDirection_signedExtremalEigenspaces_le_ker_first
    (A B : E →L[ℂ] E)
    (hplus : ‖A + B‖ ≤ 1)
    (hminus : ‖A - B‖ ≤ 1) :
    (Module.End.eigenspace (B : E →ₗ[ℂ] E) 1 ⊔
      Module.End.eigenspace (B : E →ₗ[ℂ] E) (-1)) ≤
      LinearMap.ker (A : E →ₗ[ℂ] E) := by
  apply sup_le
  · exact twoDirection_unitEigenspace_le_ker_first
      A B hplus hminus 1 (by norm_num)
  · exact twoDirection_unitEigenspace_le_ker_first
      A B hplus hminus (-1) (by norm_num)

end Neoplatonic.LTR
