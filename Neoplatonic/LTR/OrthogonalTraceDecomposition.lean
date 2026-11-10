import Neoplatonic.LTR.TwoDimensionalPauliResidual
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic

/-!
# LTR-MAN-62: trace decomposition across an invariant orthogonal complement

MAN-60 proves that the residual space of four signed extremal
eigenvectors is invariant under both Dirac coordinate operators.
MAN-61 gives the Pauli normal form when its compressed operator
has complex dimension two and vanishing trace.

Here we establish the general finite-dimensional trace bridge:
if a linear operator preserves a submodule K and its orthogonal
complement Kᗮ, its ambient trace is exactly the sum of the traces
on those two invariant summands.

This uses Mathlib's true internal direct sum and the
LinearMap.trace_eq_sum_trace_restrict theorem.
The remaining application is to compute the zero trace of each
coordinate operator on the signed extremal quartet's span,
deducing trace zero for the residual compression.
-/

namespace Neoplatonic.LTR

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]

/-- A two-summand family consisting of a finite-dimensional
complex Hilbert subspace and its orthogonal complement. -/
noncomputable def orthogonalTwoSummands
    (K : Submodule ℂ E) : Fin 2 → Submodule ℂ E :=
  fun i => if i = 0 then K else Kᗮ

/-- The pair K and Kᗮ gives an internal direct sum of the
ambient finite-dimensional complex Hilbert space. -/
theorem orthogonalTwoSummands_isInternal
    (K : Submodule ℂ E) :
    DirectSum.IsInternal (orthogonalTwoSummands K) := by
  classical
  have htwo : (Set.univ : Set (Fin 2)) = {(0 : Fin 2), (1 : Fin 2)} := by
    ext i
    fin_cases i <;> simp
  apply (DirectSum.isInternal_submodule_iff_isCompl
    (orthogonalTwoSummands K) (i := (0 : Fin 2))
    (j := (1 : Fin 2)) (by decide) htwo).mpr
  simpa [orthogonalTwoSummands] using K.isCompl_orthogonal

/-- The trace of an operator preserving K and Kᗮ is the sum of
its two true restricted traces, with no matrix-coordinate choices. -/
theorem orthogonalTwoSummands_trace
    (K : Submodule ℂ E) (T : E →ₗ[ℂ] E)
    (hK : ∀ x ∈ K, T x ∈ K)
    (hR : ∀ x ∈ Kᗮ, T x ∈ Kᗮ) :
    LinearMap.trace ℂ E T =
      LinearMap.trace ℂ K (T.restrict hK) +
        LinearMap.trace ℂ Kᗮ (T.restrict hR) := by
  classical
  have hmaps : ∀ i : Fin 2,
      Set.MapsTo T (orthogonalTwoSummands K i)
        (orthogonalTwoSummands K i) := by
    intro i
    fin_cases i
    · intro x hx
      exact hK x (by simpa [orthogonalTwoSummands] using hx)
    · intro x hx
      exact hR x (by simpa [orthogonalTwoSummands] using hx)
  have h := DirectSum.IsInternal.trace_eq_sum_trace_restrict
    (orthogonalTwoSummands_isInternal K) (f := T) hmaps
  simpa [orthogonalTwoSummands, Fin.sum_univ_two] using h

end Neoplatonic.LTR
