import Neoplatonic.LTR.ComplexSpectralCFCSqrt

/-!
# Compactness of every positive spectral power of the concrete Dirac

The v0.48 rank-two nuclear expansion gives norm convergence of
finite-rank operators. The limit is the actual infinite-dimensional
spectral-power map A_p, hence compact by norm-closure of the ideal
of compact bounded operators.

The result holds for every p > 0 and arbitrary real edge couplings.
-/

namespace Neoplatonic.LTR

open Filter

/-- Every actual complex spectral-power operator is compact for
all strictly positive real exponents. -/
theorem chosenComplexSpectralPower_isCompact
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    IsCompactOperator (chosenComplexSpectralPowerCLM scale p hp) := by
  have hsum :
      Tendsto (fun N : ℕ =>
        ∑ j ∈ Finset.range N, complexSingleSpectralPowerBlock scale p j)
        atTop
        (nhds (∑' j : ℕ, complexSingleSpectralPowerBlock scale p j)) :=
    (complexSingleSpectralPowerBlock_summable scale p hp).hasSum.tendsto_sum_nat
  have hlimit :
      Tendsto (finiteComplexSpectralPower scale p) atTop
        (nhds (chosenComplexSpectralPowerCLM scale p hp)) := by
    rw [chosenComplexSpectralPower_eq_tsum_rankTwo scale p hp]
    simpa only [finiteComplexSpectralPower] using hsum
  exact isCompactOperator_of_tendsto hlimit
    (Filter.Eventually.of_forall
      (finiteComplexSpectralPower_compact scale p))

end Neoplatonic.LTR
