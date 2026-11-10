import Neoplatonic.LTR.FiveFibreAtomicJointSpectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

/-!
# LTR-MAN-48: four orthogonal atomic ranges form a Hilbert-space sum

The four nonzero pairwise-orthogonal Hermitian idempotent matrices
of a faithful truth-atom resolution act as orthogonal projections.
Their ranges are pairwise orthogonal Hilbert subspaces. The sum of
the four projections is the identity, so their ranges span the
entire five-dimensional Hilbert space.

Mathlib's orthogonal direct-sum construction then provides an
orthonormal basis of ℂ^5 subordinate to the four atomic ranges,
with each basis coordinate assigned its truth-atom label.
Surjectivity of that label and reconstruction of the original
representation from its diagonal chart are subsequent obligations.
-/

namespace Neoplatonic.LTR

private abbrev FiveAtomicH := EuclideanSpace ℂ (Fin 5)
private abbrev FiveAtomicMat := Matrix (Fin 5) (Fin 5) ℂ

/-- The Hilbert range of one atomic projection. -/
noncomputable def FiveFibreAtomicResolution.atomicRange
    (P : FiveFibreAtomicResolution) (v : Fin 4) :
    Submodule ℂ FiveAtomicH :=
  ((P.proj v).toEuclideanLin).range

/-- Distinct atomic ranges are orthogonal in the actual
five-dimensional complex inner product. -/
theorem FiveFibreAtomicResolution.atomicRange_orthogonal
    (P : FiveFibreAtomicResolution)
    (v w : Fin 4) (hvw : v ≠ w)
    {x y : FiveAtomicH}
    (hx : x ∈ P.atomicRange v) (hy : y ∈ P.atomicRange w) :
    inner ℂ x y = 0 := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  have hm := congrArg
    (fun M : FiveAtomicMat => M.toEuclideanLin)
    (P.orthogonal v w hvw)
  have hcomp :
      ((P.proj v).toEuclideanLin).comp
        ((P.proj w).toEuclideanLin) = 0 := by
    simpa only [fiveFibreSquare_toEuclidean_mul, map_zero] using hm
  have hzero :
      (P.proj v).toEuclideanLin
        ((P.proj w).toEuclideanLin b) = 0 := by
    have h := congrArg
      (fun T : FiveAtomicH →ₗ[ℂ] FiveAtomicH => T b) hcomp
    simpa using h
  calc
    inner ℂ ((P.proj v).toEuclideanLin a)
        ((P.proj w).toEuclideanLin b) =
      inner ℂ a ((P.proj v).toEuclideanLin
        ((P.proj w).toEuclideanLin b)) :=
      P.symmetric v a ((P.proj w).toEuclideanLin b)
    _ = 0 := by rw [hzero]; simp

/-- The four atomic Hilbert subspaces form an orthogonal family. -/
theorem FiveFibreAtomicResolution.atomicRanges_orthogonal
    (P : FiveFibreAtomicResolution) :
    OrthogonalFamily ℂ
      (fun v : Fin 4 => ↥(P.atomicRange v))
      (fun v : Fin 4 => (P.atomicRange v).subtypeₗᵢ) := by
  intro v w hvw x y
  exact P.atomicRange_orthogonal v w hvw x.property y.property

/-- The four atomic ranges span the entire five-dimensional
complex Hilbert space, using the completeness identity sum P_v = I. -/
theorem FiveFibreAtomicResolution.atomicRanges_span
    (P : FiveFibreAtomicResolution) :
    (⨆ v : Fin 4, P.atomicRange v) = ⊤ := by
  classical
  apply top_unique
  intro x hx
  have hdecomp : (∑ v : Fin 4,
      (P.proj v).toEuclideanLin x) = x := by
    calc
      (∑ v : Fin 4, (P.proj v).toEuclideanLin x) =
          ((∑ v : Fin 4, P.proj v).toEuclideanLin) x := by
        simp
      _ = x := by
        rw [P.sum_one]
        simp [Matrix.toLpLin_one]
  have hmem :
      (∑ v : Fin 4, (P.proj v).toEuclideanLin x) ∈
        (⨆ v : Fin 4, P.atomicRange v) := by
    apply Submodule.sum_mem
    intro v hv
    exact (le_iSup (fun w : Fin 4 => P.atomicRange w) v)
      (show (P.proj v).toEuclideanLin x ∈ P.atomicRange v from ⟨x, rfl⟩)
  simpa only [hdecomp] using hmem

/-- The four ranges supply an internal orthogonal decomposition
of the genuine complex Hilbert space. -/
theorem FiveFibreAtomicResolution.atomicRanges_internal
    (P : FiveFibreAtomicResolution) :
    DirectSum.IsInternal (fun v : Fin 4 => P.atomicRange v) := by
  classical
  apply (P.atomicRanges_orthogonal.isInternal_iff).2
  rw [P.atomicRanges_span]
  simp

/-- A simultaneous orthonormal basis subordinate to the four
atomic truth-projection ranges. -/
noncomputable def FiveFibreAtomicResolution.atomicOrthonormalBasis
    (P : FiveFibreAtomicResolution) :
    OrthonormalBasis (Fin 5) ℂ FiveAtomicH :=
  P.atomicRanges_internal.subordinateOrthonormalBasis
    (by simp) P.atomicRanges_orthogonal

/-- The truth atom associated with each orthonormal basis vector,
obtained from the orthogonal direct-sum decomposition. -/
noncomputable def FiveFibreAtomicResolution.atomicBasisLabel
    (P : FiveFibreAtomicResolution) : Fin 5 → Fin 4 :=
  fun i => P.atomicRanges_internal.subordinateOrthonormalBasisIndex
    (by simp) i P.atomicRanges_orthogonal

/-- Every chosen basis vector belongs to the atomic range
assigned by its diagonal truth label. -/
theorem FiveFibreAtomicResolution.atomicBasis_subordinate
    (P : FiveFibreAtomicResolution) (i : Fin 5) :
    P.atomicOrthonormalBasis i ∈ P.atomicRange (P.atomicBasisLabel i) := by
  exact P.atomicRanges_internal.subordinateOrthonormalBasis_subordinate
    (by simp) i P.atomicRanges_orthogonal

end Neoplatonic.LTR
