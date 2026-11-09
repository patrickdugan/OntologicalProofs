import Neoplatonic.LTR.FiveFibreSquareOrientations
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

/-!
# LTR-MAN-27: opposite-corner witnesses are forced by Hamming geodesics

Suppose a norm-constrained complex observable on the Boolean square
attains the opposite-corner difference 2, while all four square edges
obey the Hamming-one dual upper bound. Each intermediate value lies
in both closed unit discs centered at 0 and 2. Their intersection
is exactly the singleton {1}.

The two normalized opposite-corner witnesses are therefore uniquely
the coordinate sum and translated coordinate difference:
  g = (0, 1, 1, 2)
  h = (1, 0, 2, 1).

The final theorem supplies these concrete admissible witnesses from
a generic dual seminorm L and normalized opposite-distance witnesses.
The subsequent analytic obligation is to derive the normalized
attaining witnesses from exact Connes distance 2 in the finite
spectral representation, and then use the actual matrix commutator
to obtain the two operator contraction inequalities.
-/

namespace Neoplatonic.LTR

/-- Two complex closed unit discs tangent at 1 meet only at 1. -/
theorem complex_two_unit_discs_tangent
    (z : ℂ) (hz0 : ‖z‖ ≤ 1)
    (hz2 : ‖(2 : ℂ) - z‖ ≤ 1) :
    z = 1 := by
  have hsq0 : ‖z‖ ^ 2 ≤ (1 : ℝ) := by
    simpa using (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr hz0
  have hsq2 : ‖(2 : ℂ) - z‖ ^ 2 ≤ (1 : ℝ) := by
    simpa using (sq_le_sq₀ (norm_nonneg _) (by norm_num)).mpr hz2
  rw [Complex.sq_norm, Complex.normSq_apply] at hsq0 hsq2
  have hre2 : ((2 : ℂ) - z).re = 2 - z.re := by simp
  have him2 : ((2 : ℂ) - z).im = -z.im := by simp
  rw [hre2, him2] at hsq2
  have hre : z.re = 1 := by
    nlinarith [sq_nonneg (z.re - 1), sq_nonneg z.im]
  have him : z.im = 0 := by
    nlinarith [sq_nonneg (z.re - 1), sq_nonneg z.im]
  apply Complex.ext
  · simpa using hre
  · simpa using him

/-- Hamming distance-to-00 witness in the four-vertex order
00, 01, 10, 11. -/
def twoBitOppositeCornerSum (i : Fin 4) : ℂ :=
  if i = 0 then 0 else if i = 3 then 2 else 1

/-- Translated Hamming coordinate difference, attaining the
distance from 01 to 10. -/
def twoBitOppositeCornerDifference (i : Fin 4) : ℂ :=
  if i = 1 then 0 else if i = 2 then 2 else 1

/-- Equality along both Hamming geodesics from 00 to 11 fixes
the intermediate complex values at 1. -/
theorem twoBitOppositeCornerSum_unique
    (f : Fin 4 → ℂ)
    (h0 : f 0 = 0) (h3 : f 3 = 2)
    (h01 : ‖f 0 - f 1‖ ≤ 1)
    (h02 : ‖f 0 - f 2‖ ≤ 1)
    (h13 : ‖f 3 - f 1‖ ≤ 1)
    (h23 : ‖f 3 - f 2‖ ≤ 1) :
    f = twoBitOppositeCornerSum := by
  have h1 : f 1 = 1 :=
    complex_two_unit_discs_tangent (f 1)
      (by simpa [h0] using h01) (by simpa [h3] using h13)
  have h2 : f 2 = 1 :=
    complex_two_unit_discs_tangent (f 2)
      (by simpa [h0] using h02) (by simpa [h3] using h23)
  funext i
  fin_cases i <;>
    simp [twoBitOppositeCornerSum, h0, h1, h2, h3]

/-- Equality along both Hamming geodesics from 01 to 10 fixes
the other two complex values at 1. -/
theorem twoBitOppositeCornerDifference_unique
    (f : Fin 4 → ℂ)
    (h1 : f 1 = 0) (h2 : f 2 = 2)
    (h01 : ‖f 0 - f 1‖ ≤ 1)
    (h02 : ‖f 0 - f 2‖ ≤ 1)
    (h13 : ‖f 3 - f 1‖ ≤ 1)
    (h23 : ‖f 3 - f 2‖ ≤ 1) :
    f = twoBitOppositeCornerDifference := by
  have h20 : ‖f 2 - f 0‖ ≤ 1 := by
    rw [norm_sub_rev]
    exact h02
  have h23' : ‖f 2 - f 3‖ ≤ 1 := by
    rw [norm_sub_rev]
    exact h23
  have h0 : f 0 = 1 :=
    complex_two_unit_discs_tangent (f 0)
      (by simpa [h1] using h01)
      (by simpa [h2] using h20)
  have h3 : f 3 = 1 :=
    complex_two_unit_discs_tangent (f 3)
      (by simpa [h1] using h13)
      (by simpa [h2] using h23')
  funext i
  fin_cases i <;>
    simp [twoBitOppositeCornerDifference, h0, h1, h2, h3]

/-- Any dual seminorm whose unit ball has the four unit-edge upper
bounds must admit the exact canonical sum/difference observables,
provided the normalized opposite-distance suprema are attained. -/
theorem twoBitOppositeAttainers_force_coordinateWitnesses
    (L : (Fin 4 → ℂ) → ℝ)
    (hupper : ∀ f : Fin 4 → ℂ, L f ≤ 1 →
      ‖f 0 - f 1‖ ≤ 1 ∧
      ‖f 0 - f 2‖ ≤ 1 ∧
      ‖f 3 - f 1‖ ≤ 1 ∧
      ‖f 3 - f 2‖ ≤ 1)
    (hsum : ∃ f : Fin 4 → ℂ, L f ≤ 1 ∧
      f 0 = 0 ∧ f 3 = 2)
    (hdiff : ∃ f : Fin 4 → ℂ, L f ≤ 1 ∧
      f 1 = 0 ∧ f 2 = 2) :
    L twoBitOppositeCornerSum ≤ 1 ∧
      L twoBitOppositeCornerDifference ≤ 1 := by
  constructor
  · obtain ⟨f, hf, h0, h3⟩ := hsum
    obtain ⟨h01, h02, h13, h23⟩ := hupper f hf
    have heq := twoBitOppositeCornerSum_unique
      f h0 h3 h01 h02 h13 h23
    rw [heq] at hf
    exact hf
  · obtain ⟨f, hf, h1, h2⟩ := hdiff
    obtain ⟨h01, h02, h13, h23⟩ := hupper f hf
    have heq := twoBitOppositeCornerDifference_unique
      f h1 h2 h01 h02 h13 h23
    rw [heq] at hf
    exact hf

end Neoplatonic.LTR
