import Neoplatonic.Arithmetic
import Mathlib.Tactic

/-!
# A positive norm constructed from finite divisibility

Index Fin N represents integers 1 through N. The feature at d sums the
coefficients whose indices are multiples of d. Its squared norm is positive
without RH or any ontological premise. No identity with Weil's form is claimed.
-/

noncomputable section
open scoped BigOperators
namespace GrammyAndPrimes.DivisorGram

/-- The finite divisibility-incidence transform, with zero excluded. -/
def divisorAmplitude (N : ℕ) (v : Fin N → ℝ) (d : Fin N) : ℝ :=
  ∑ n : Fin N, if (d.val + 1) ∣ (n.val + 1) then v n else 0

/-- The Gram energy of the independently specified incidence transform. -/
def divisorEnergy (N : ℕ) (v : Fin N → ℝ) : ℝ :=
  ∑ d : Fin N, (divisorAmplitude N v d) ^ 2

theorem divisor_energy_nonnegative (N : ℕ) (v : Fin N → ℝ) :
    0 ≤ divisorEnergy N v :=
  Finset.sum_nonneg (fun d _ => sq_nonneg (divisorAmplitude N v d))

/-- The unit divisor supplies the common feature of all positive integers. -/
theorem unit_amplitude (N : ℕ) (v : Fin (N + 1) → ℝ) :
    divisorAmplitude (N + 1) v 0 = ∑ n : Fin (N + 1), v n := by
  simp [divisorAmplitude]

/-- The same alternating coefficients used in the reflection countermodel
have positive divisor energy. The two quadratic forms are different. -/
theorem two_point_divisor_energy :
    divisorEnergy 2 (fun i : Fin 2 => if i = 0 then 1 else -1) = 1 := by
  norm_num [divisorEnergy, divisorAmplitude, Fin.sum_univ_two]

#print axioms divisor_energy_nonnegative
#print axioms unit_amplitude
#print axioms two_point_divisor_energy

end GrammyAndPrimes.DivisorGram
