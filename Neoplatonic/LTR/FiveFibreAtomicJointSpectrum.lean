import Neoplatonic.LTR.FiveFibreFaithfulDiagonalNoGo
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Tactic

/-!
# LTR-MAN-47: the joint spectrum of four atomic truth projections

A faithful unital representation of the four-atom complex truth algebra
provides four nonzero Hermitian idempotents. Distinct atoms have
orthogonal products, and their sum is the identity.

These hypotheses give an elementary finite-dimensional resolution of
the identity. After transporting the matrices to linear maps on the
actual complex Hilbert space ℂ^5, the atomic operators are symmetric
and commute pairwise. Mathlib's theorem for joint eigenspaces of
commuting symmetric maps proves that their common eigenspaces span
the entire Hilbert space.

This is the spectral ingredient for choosing a simultaneous
orthonormal eigenbasis and recovering a surjective five-coordinate
truth labeling in the arbitrary faithful representation case.
-/

namespace Neoplatonic.LTR

private abbrev FiveTruthMatrix := Matrix (Fin 5) (Fin 5) ℂ
private abbrev FiveTruthH := EuclideanSpace ℂ (Fin 5)

/-- A faithful four-atom orthogonal resolution of the identity
in the five-dimensional complex matrix algebra. -/
structure FiveFibreAtomicResolution where
  proj : Fin 4 → FiveTruthMatrix
  hermitian : ∀ v : Fin 4, (proj v).IsHermitian
  idempotent : ∀ v : Fin 4, proj v * proj v = proj v
  orthogonal : ∀ v w : Fin 4, v ≠ w → proj v * proj w = 0
  sum_one : (∑ v : Fin 4, proj v) = 1
  nonzero : ∀ v : Fin 4, proj v ≠ 0

/-- The atomic projections commute as matrices. -/
theorem FiveFibreAtomicResolution.commute
    (P : FiveFibreAtomicResolution) (v w : Fin 4) :
    Commute (P.proj v) (P.proj w) := by
  by_cases hvw : v = w
  · subst w
    exact Commute.refl _
  · change P.proj v * P.proj w = P.proj w * P.proj v
    calc
      P.proj v * P.proj w = 0 := P.orthogonal v w hvw
      _ = P.proj w * P.proj v := (P.orthogonal w v hvw.symm).symm

/-- The linear operators associated to all atomic projections
are symmetric on the genuine complex Euclidean Hilbert space. -/
theorem FiveFibreAtomicResolution.symmetric
    (P : FiveFibreAtomicResolution) (v : Fin 4) :
    (P.proj v).toEuclideanLin.IsSymmetric :=
  Matrix.isSymmetric_toEuclideanLin_iff.mpr (P.hermitian v)

/-- The linear operators associated to atomic projections commute. -/
theorem FiveFibreAtomicResolution.commute_linear
    (P : FiveFibreAtomicResolution) (v w : Fin 4) :
    Commute
      ((P.proj v).toEuclideanLin : FiveTruthH →ₗ[ℂ] FiveTruthH)
      ((P.proj w).toEuclideanLin : FiveTruthH →ₗ[ℂ] FiveTruthH) := by
  have hm : P.proj v * P.proj w = P.proj w * P.proj v :=
    P.commute v w
  have h := congrArg
    (fun M : FiveTruthMatrix => M.toEuclideanLin) hm
  simpa only [fiveFibreSquare_toEuclidean_mul, Module.End.mul_eq_comp]
    using h

/-- The common eigenspaces of the four truth-atom projections span
the entire five-dimensional complex Hilbert space. This includes
repeated joint eigenvalues and is independent of the multiplicity
pattern of the chosen representation. -/
theorem FiveFibreAtomicResolution.jointEigenspaces_span
    (P : FiveFibreAtomicResolution) :
    (⨆ χ : Fin 4 → ℂ,
      ⨅ v : Fin 4,
        (P.proj v).toEuclideanLin.eigenspace (χ v)) = ⊤ := by
  classical
  let T : Fin 4 → (FiveTruthH →ₗ[ℂ] FiveTruthH) :=
    fun v => (P.proj v).toEuclideanLin
  have hT : ∀ v : Fin 4, (T v).IsSymmetric := by
    intro v
    exact P.symmetric v
  have hC : Pairwise (Function.onFun Commute T) := by
    intro v w _
    exact P.commute_linear v w
  exact LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute hT hC

end Neoplatonic.LTR
