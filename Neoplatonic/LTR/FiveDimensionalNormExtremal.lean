import Neoplatonic.LTR.FiveDimensionalSignedVectors
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# LTR-MAN-20: attaining extremal signed eigenvalues from the operator norm

For a self-adjoint norm-one continuous operator on a finite-dimensional
complex Hilbert space, the spectral radius is one and is attained in
its complex spectrum. Finite dimensionality makes the operator compact,
and the Fredholm alternative supplies an actual nonzero eigenvector.
Self-adjointness forces its eigenvalue to be real. Unit modulus and
reality imply that the eigenvalue is one of +1, -1.

This completes the existence premise required to pair extremal vectors
with the grading involution in MAN-14, and pass them to MAN-19.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [CompleteSpace E]

/-- A self-adjoint norm-one operator on a finite-dimensional complex Hilbert
space has a genuine nonzero eigenvector at an eigenvalue +1 or -1. -/
theorem normOneSelfAdjoint_exists_signedEigenvector
    (T : E →L[ℂ] E)
    (hself : IsSelfAdjoint T)
    (hnorm : ‖T‖ = 1) :
    ∃ (μ : ℂ) (w : E), (μ = 1 ∨ μ = -1) ∧
      w ≠ 0 ∧ T w = μ • w := by
  classical
  haveI : Nontrivial E := by
    by_contra hn
    haveI : Subsingleton E := not_nontrivial_iff_subsingleton.mp hn
    have hzero : T = 0 := by
      ext x
      exact Subsingleton.elim _ _
    simp [hzero] at hnorm
  haveI : ProperSpace E := FiniteDimensional.proper_rclike ℂ E
  have hcompact : IsCompactOperator T :=
    isCompactOperator_of_locallyCompactSpace_dom T
  obtain ⟨μ, hspec, hrad⟩ :=
    spectrum.exists_nnnorm_eq_spectralRadius T
  have hnn : (‖μ‖₊ : ℝ≥0∞) = (‖T‖₊ : ℝ≥0∞) := by
    rw [hrad, T.spectralRadius_eq_nnnorm hself]
  have hnn' : ‖μ‖₊ = ‖T‖₊ := ENNReal.coe_injective hnn
  have hμnorm : ‖μ‖ = 1 := by
    have h := congrArg (fun r : ℝ≥0 => (r : ℝ)) hnn'
    simpa only [coe_nnnorm] using h.trans hnorm
  have hμne : μ ≠ 0 := by
    intro hz
    simp [hz] at hμnorm
  have heig : Module.End.HasEigenvalue (T : Module.End ℂ E) μ :=
    (hcompact.hasEigenvalue_iff_mem_spectrum hμne).mpr hspec
  have hsym : T.toLinearMap.IsSymmetric := by
    intro x y
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hself) x y
  have hconj : conj μ = μ :=
    LinearMap.IsSymmetric.conj_eigenvalue_eq_self hsym heig
  have hsq : μ ^ 2 = 1 := by
    calc
      μ ^ 2 = μ * conj μ := by rw [hconj]; ring
      _ = (‖μ‖ : ℂ) ^ 2 := by simpa using Complex.mul_conj' μ
      _ = 1 := by simp [hμnorm]
  obtain ⟨w, hw⟩ := heig.exists_hasEigenvector
  exact ⟨μ, w, sq_eq_one_iff.mp hsq, hw.2,
    Module.End.mem_eigenspace_iff.mp hw.1⟩

end Neoplatonic.LTR
