import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# LTR-MAN-12: parallelogram contraction certificate for two Dirac directions

The two-bit Hamming no-go argument introduces the self-adjoint
commutators A = i[D,p] and B = i[D,q]. Exact opposite-corner
distances give norm bounds on A+B and A-B.

The parallelogram identity then bounds the total squared action of
both operators on any vector, even without self-adjointness. Whenever
one operator acts isometrically on a vector, the other annihilates it.

These are universal normed complex Hilbert-space results, proven here
without finite-dimensionality, spectral decomposition, unverified
axioms, or a named Dirac matrix. The subsequent eigenspace and
multiplicity obstruction requires separate formalization.
-/

namespace Neoplatonic.LTR

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Norm-one bounds on the sum and difference of two bounded
Hilbert operators imply a pointwise Pythagorean contraction. -/
theorem twoDirection_parallelogram_contraction
    (A B : E →L[ℂ] E)
    (hplus : ‖A + B‖ ≤ 1)
    (hminus : ‖A - B‖ ≤ 1)
    (v : E) :
    ‖A v‖ ^ 2 + ‖B v‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have hp : ‖(A + B) v‖ ≤ ‖v‖ := by
    calc
      ‖(A + B) v‖ ≤ ‖A + B‖ * ‖v‖ := (A + B).le_opNorm v
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hplus (norm_nonneg v)
      _ = ‖v‖ := one_mul _
  have hm : ‖(A - B) v‖ ≤ ‖v‖ := by
    calc
      ‖(A - B) v‖ ≤ ‖A - B‖ * ‖v‖ := (A - B).le_opNorm v
      _ ≤ 1 * ‖v‖ := mul_le_mul_of_nonneg_right hminus (norm_nonneg v)
      _ = ‖v‖ := one_mul _
  have hpsq : ‖(A + B) v‖ ^ 2 ≤ ‖v‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hp
  have hmsq : ‖(A - B) v‖ ^ 2 ≤ ‖v‖ ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hm
  have hpar := parallelogram_law_with_norm_mul ℂ (A v) (B v)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply] at hpsq hmsq
  nlinarith [hpar]

/-- If the first contraction achieves its full norm on a vector,
then the second direction vanishes there. -/
theorem twoDirection_first_saturating_annihilates_second
    (A B : E →L[ℂ] E)
    (hplus : ‖A + B‖ ≤ 1)
    (hminus : ‖A - B‖ ≤ 1)
    (v : E)
    (hsaturates : ‖A v‖ = ‖v‖) :
    B v = 0 := by
  have h := twoDirection_parallelogram_contraction A B hplus hminus v
  rw [hsaturates] at h
  have hn : ‖B v‖ = 0 := by
    have hnonneg := norm_nonneg (B v)
    nlinarith
  exact norm_eq_zero.mp hn

/-- The same statement holds with the directions interchanged. -/
theorem twoDirection_second_saturating_annihilates_first
    (A B : E →L[ℂ] E)
    (hplus : ‖A + B‖ ≤ 1)
    (hminus : ‖A - B‖ ≤ 1)
    (v : E)
    (hsaturates : ‖B v‖ = ‖v‖) :
    A v = 0 := by
  have hswapPlus : ‖B + A‖ ≤ 1 := by simpa only [add_comm] using hplus
  have hswapMinus : ‖B - A‖ ≤ 1 := by
    have heq : B - A = -(A - B) := by abel
    rw [heq, norm_neg]
    exact hminus
  exact twoDirection_first_saturating_annihilates_second
    B A hswapPlus hswapMinus v hsaturates

end Neoplatonic.LTR
