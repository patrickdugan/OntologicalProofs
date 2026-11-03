import Neoplatonic.LTR.DensePairMarking
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exponential spectral-energy summability for every positive exponent

The verified Dirac block has D_j² = (4^j + s_j²) I₂.
For any real p > 0, its two positive energy terms

   2 * (1 + 4^j + s_j²)^(-p/2)

are summable. The proof compares the squared-resolvent weight
against (1/4)^j and then applies monotonicity of positive real
powers and convergence of a geometric series.

The theorem concerns the scalar trace contribution of each finite
block. A global trace-class operator theorem, if needed for a
specific Mathlib Schatten-class API, is a separate packaging step.
-/

namespace Neoplatonic.LTR

/-- The coefficient of the squared resolvent is bounded by a
geometric factor, uniformly in the arbitrary real edge coupling. -/
theorem chosenSquaredResolventWeight_le_geometric
    (scale : ℕ → ℝ) (j : ℕ) :
    chosenSquaredResolventWeight scale j ≤ ((4 : ℝ)⁻¹)^j := by
  have hp : (0 : ℝ) < (4 : ℝ)^j := by positivity
  have hden : (4 : ℝ)^j ≤ 1 + (4 : ℝ)^j := by linarith
  have h := one_div_le_one_div_of_le hp hden
  calc
    chosenSquaredResolventWeight scale j ≤ squaredResolventTail j :=
      chosenSquaredResolventWeight_le_tail scale j
    _ = (1 + (4 : ℝ)^j)⁻¹ := rfl
    _ ≤ ((4 : ℝ)^j)⁻¹ := by simpa only [one_div] using h
    _ = ((4 : ℝ)⁻¹)^j := by rw [inv_pow]

/-- Every strictly positive real power of the squared-resolvent
coefficient is summable, independently of the coupling sequence. -/
theorem chosenSquaredResolventWeight_rpow_summable
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    Summable (fun j : ℕ =>
      (chosenSquaredResolventWeight scale j)^p) := by
  have hbase : (0 : ℝ) ≤ (4 : ℝ)⁻¹ := by norm_num
  have hsmall : (4 : ℝ)⁻¹ < 1 := by norm_num
  have hgeom : Summable (fun j : ℕ => (((4 : ℝ)⁻¹)^p)^j) :=
    summable_geometric_of_lt_one
      (Real.rpow_nonneg hbase p)
      (Real.rpow_lt_one hbase hsmall hp)
  refine Summable.of_nonneg_of_le
    (fun j => Real.rpow_nonneg
      (chosenSquaredResolventWeight_nonneg scale j) p)
    (fun j => ?_) hgeom
  calc
    (chosenSquaredResolventWeight scale j)^p ≤
        (((4 : ℝ)⁻¹)^j)^p :=
      Real.rpow_le_rpow
        (chosenSquaredResolventWeight_nonneg scale j)
        (chosenSquaredResolventWeight_le_geometric scale j)
        hp.le
    _ = (((4 : ℝ)⁻¹)^p)^j := by
      rw [← Real.rpow_natCast_mul hbase j p,
        mul_comm (j : ℝ) p, Real.rpow_mul_natCast hbase p j]

/-- The two singular-energy contributions from a complex two-point
Dirac block at exponent p > 0. -/
noncomputable def complexSpectralTraceTerm
    (scale : ℕ → ℝ) (p : ℝ) (j : ℕ) : ℝ :=
  2 * (chosenSquaredResolventWeight scale j)^(p / 2)

/-- The sum of all two-dimensional scalar spectral trace
contributions is finite for every p > 0. -/
theorem complexSpectralTraceTerm_summable
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    Summable (complexSpectralTraceTerm scale p) := by
  have hp2 : 0 < p / 2 := by linarith
  change Summable (fun j : ℕ =>
    2 * (chosenSquaredResolventWeight scale j)^(p / 2))
  exact (chosenSquaredResolventWeight_rpow_summable scale
    (p / 2) hp2).mul_left 2

/-- The usual regularized-energy expression agrees with the
squared-resolvent weight raised to p/2. -/
theorem complexSpectralTraceTerm_eq_energy
    (scale : ℕ → ℝ) (p : ℝ) (j : ℕ) :
    complexSpectralTraceTerm scale p j =
      2 * (1 + ((2 : ℝ)^j)^2 + (scale j)^2)^(-(p / 2)) := by
  unfold complexSpectralTraceTerm chosenSquaredResolventWeight
  rw [Real.rpow_neg_eq_inv_rpow]

end Neoplatonic.LTR
