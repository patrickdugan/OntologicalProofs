import Neoplatonic.LTR.FiveFibreAtomicRangeDecomposition
import Mathlib.Tactic

/-!
# LTR-MAN-49: atomic basis labels are faithful, with joint eigenvectors

The subordinate orthonormal basis from MAN-48 supplies exactly five
Hilbert coordinates. Nonzero atomic projectors have nonzero ranges,
and Mathlib's subordinate-basis index theorem produces at least one
basis vector in each range. Thus its recovered truth labeling is
surjective.

Every projector acts on a basis vector by the indicator of that
vector's truth atom. The resulting coordinate eigenvalue identity
is the next bridge to matrix diagonalization and unitary conjugation
of arbitrary faithful four-atom representations.
-/

namespace Neoplatonic.LTR

private abbrev FiveAtomicH := EuclideanSpace ℂ (Fin 5)
private abbrev FiveAtomicMat := Matrix (Fin 5) (Fin 5) ℂ

/-- The range of a nonzero atomic projection is a nonzero submodule. -/
theorem FiveFibreAtomicResolution.atomicRange_nonzero
    (P : FiveFibreAtomicResolution) (v : Fin 4) :
    P.atomicRange v ≠ ⊥ := by
  intro hz
  have hr : ((P.proj v).toEuclideanLin).range = ⊥ := by
    simpa only [FiveFibreAtomicResolution.atomicRange] using hz
  have hlin : (P.proj v).toEuclideanLin = 0 :=
    LinearMap.range_eq_bot.mp hr
  exact P.nonzero v (Matrix.toEuclideanLin.injective hlin)

/-- Every truth atom has at least one coordinate in the subordinate
orthonormal basis, so its label map is faithful. -/
theorem FiveFibreAtomicResolution.atomicBasisLabel_surjective
    (P : FiveFibreAtomicResolution) :
    Function.Surjective P.atomicBasisLabel := by
  intro v
  have hnonzero : P.atomicRange v ≠ ⊥ := P.atomicRange_nonzero v
  obtain ⟨i, hi⟩ :=
    P.atomicRanges_internal.exists_subordinateOrthonormalBasisIndex_eq
      (by simp : Module.finrank ℂ FiveAtomicH = 5)
      P.atomicRanges_orthogonal hnonzero
  refine ⟨i, ?_⟩
  exact hi

/-- On an atomic range, every atomic projector acts either
as identity on its own atom or zero on an orthogonal atom. -/
theorem FiveFibreAtomicResolution.atomicProjection_onRange
    (P : FiveFibreAtomicResolution)
    (v w : Fin 4) {x : FiveAtomicH}
    (hx : x ∈ P.atomicRange w) :
    (P.proj v).toEuclideanLin x = if v = w then x else 0 := by
  rcases hx with ⟨y, rfl⟩
  split_ifs with h
  · subst w
    have hm := congrArg
      (fun M : FiveAtomicMat => M.toEuclideanLin)
      (P.idempotent v)
    have hcomp :
        ((P.proj v).toEuclideanLin).comp
          ((P.proj v).toEuclideanLin) =
          (P.proj v).toEuclideanLin := by
      simpa only [fiveFibreSquare_toEuclidean_mul] using hm
    have hy := congrArg
      (fun T : FiveAtomicH →ₗ[ℂ] FiveAtomicH => T y) hcomp
    simpa using hy
  · have hm := congrArg
      (fun M : FiveAtomicMat => M.toEuclideanLin)
      (P.orthogonal v w h)
    have hcomp :
        ((P.proj v).toEuclideanLin).comp
          ((P.proj w).toEuclideanLin) = 0 := by
      simpa only [fiveFibreSquare_toEuclidean_mul, map_zero] using hm
    have hy := congrArg
      (fun T : FiveAtomicH →ₗ[ℂ] FiveAtomicH => T y) hcomp
    simpa using hy

/-- The subordinate orthonormal basis diagonalizes every atom:
the eigenvalues are the indicator functions of its recovered labels. -/
theorem FiveFibreAtomicResolution.atomicBasis_eigen
    (P : FiveFibreAtomicResolution)
    (v : Fin 4) (i : Fin 5) :
    (P.proj v).toEuclideanLin (P.atomicOrthonormalBasis i) =
      if v = P.atomicBasisLabel i then P.atomicOrthonormalBasis i else 0 := by
  exact P.atomicProjection_onRange
    v (P.atomicBasisLabel i) (P.atomicBasis_subordinate i)

end Neoplatonic.LTR
