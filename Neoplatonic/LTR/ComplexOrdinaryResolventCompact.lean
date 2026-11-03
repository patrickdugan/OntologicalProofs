import Neoplatonic.LTR.ComplexOrdinaryResolventDecay
import Neoplatonic.LTR.ComplexOrdinaryResolventFiniteRank

/-!
# Compactness of the ordinary complex Dirac resolvent

The bounded complex Hilbert operator Q=(D-iI)⁻¹ has blocks
Q_j=(D_j+iI)/(1+4^j+s_j²).
Their verified norm bounds ‖Q_j‖≤2/(2^j) imply that the
tail from index N onward has norm at most 2/(2^N).
The finite sum over j<N is compact because it factors through
finitely many two-dimensional complex Euclidean coordinate spaces.
Consequently Q is a norm-limit of compact operators and is compact.

This is the standard ordinary compact-resolvent theorem, including
a quantitative operator-norm truncation bound.
-/

namespace Neoplatonic.LTR

open Filter
open scoped lp Topology

/-- Quantitative geometric ordinary-resolvent tail bound. -/
noncomputable def complexOrdinaryResolventTailBound (N : ℕ) : ℝ :=
  2 * ((2 : ℝ)^N)⁻¹

theorem complexOrdinaryResolventTailBound_nonneg (N : ℕ) :
    0 ≤ complexOrdinaryResolventTailBound N := by
  unfold complexOrdinaryResolventTailBound
  positivity

/-- High-index ordinary resolvent blocks, zero before N. -/
noncomputable def chosenComplexOrdinaryResolventTailCLM
    (scale : ℕ → ℝ) (N : ℕ) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  lp.mapCLM 2
    (fun j => if N ≤ j then complexOrdinaryResolventBlock scale j else 0)
    (complexOrdinaryResolventTailBound_nonneg N)
    (by
      intro j
      by_cases hj : N ≤ j
      · simpa [hj, complexOrdinaryResolventTailBound] using
          complexOrdinaryResolventBlock_norm_le_tail scale N j hj
      · simpa [hj] using complexOrdinaryResolventTailBound_nonneg N)

/-- The infinite ordinary resolvent tail has an exponentially small
operator norm, uniformly in the off-diagonal scale sequence. -/
theorem chosenComplexOrdinaryResolventTailCLM_norm_le
    (scale : ℕ → ℝ) (N : ℕ) :
    ‖chosenComplexOrdinaryResolventTailCLM scale N‖ ≤
      complexOrdinaryResolventTailBound N := by
  exact lp.norm_mapCLM_le 2
    (fun j => if N ≤ j then complexOrdinaryResolventBlock scale j else 0)
    (complexOrdinaryResolventTailBound_nonneg N)
    (by
      intro j
      by_cases hj : N ≤ j
      · simpa [hj, complexOrdinaryResolventTailBound] using
          complexOrdinaryResolventBlock_norm_le_tail scale N j hj
      · simpa [hj] using complexOrdinaryResolventTailBound_nonneg N)

/-- Exact coordinatewise action of the ordinary resolvent tail. -/
theorem chosenComplexOrdinaryResolventTailCLM_apply
    (scale : ℕ → ℝ) (N : ℕ)
    (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    chosenComplexOrdinaryResolventTailCLM scale N ψ j =
      if N ≤ j then complexOrdinaryResolventBlock scale j (ψ j)
      else 0 := by
  change (if N ≤ j then complexOrdinaryResolventBlock scale j else 0)
    (ψ j) = _
  by_cases hj : N ≤ j
  · simp [hj]
  · simp [hj]

/-- The finite sum of ordinary resolvent blocks is full Q minus its tail. -/
theorem finiteComplexOrdinaryResolvent_eq_cutoff
    (scale : ℕ → ℝ) (N : ℕ) :
    finiteComplexOrdinaryResolvent scale N =
      chosenComplexOrdinaryResolventCLM scale -
        chosenComplexOrdinaryResolventTailCLM scale N := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  rw [ContinuousLinearMap.sub_apply, lp.coeFn_sub, Pi.sub_apply,
    chosenComplexOrdinaryResolventCLM_apply,
    chosenComplexOrdinaryResolventTailCLM_apply,
    finiteComplexOrdinaryResolvent_apply]
  by_cases hj : j < N
  · have hn : ¬ N ≤ j := by omega
    simp [hj, hn]
  · have hn : N ≤ j := Nat.le_of_not_gt hj
    simp [hj, hn]

/-- Exact finite-rank approximation rate for the ordinary complex
resolvent, uniform over all real off-diagonal scales. -/
theorem complexOrdinaryResolvent_finite_norm_bound
    (scale : ℕ → ℝ) (N : ℕ) :
    ‖chosenComplexOrdinaryResolventCLM scale -
       finiteComplexOrdinaryResolvent scale N‖ ≤
       complexOrdinaryResolventTailBound N := by
  rw [finiteComplexOrdinaryResolvent_eq_cutoff]
  convert chosenComplexOrdinaryResolventTailCLM_norm_le scale N using 1
  congr 1
  abel

/-- The explicit ordinary-resolvent truncation error tends to zero. -/
theorem complexOrdinaryResolventTailBound_tendsto :
    Tendsto complexOrdinaryResolventTailBound atTop (𝓝 (0 : ℝ)) := by
  have hp : Tendsto (fun N : ℕ => (2 : ℝ)^N) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hi : Tendsto (fun N : ℕ => ((2 : ℝ)^N)⁻¹) atTop
      (𝓝 (0 : ℝ)) := tendsto_inv_atTop_zero.comp hp
  have ht : Tendsto
      (fun N : ℕ => (2 : ℝ) * ((2 : ℝ)^N)⁻¹)
      atTop (𝓝 ((2 : ℝ) * 0)) :=
    tendsto_const_nhds.mul hi
  simpa only [complexOrdinaryResolventTailBound, mul_zero] using ht

/-- The actual complex ordinary resolvent (D-iI)⁻¹ is compact on
the infinite Hilbert space ℓ²(ℕ,ℂ²). -/
theorem chosenComplexOrdinaryResolvent_isCompact
    (scale : ℕ → ℝ) :
    IsCompactOperator (chosenComplexOrdinaryResolventCLM scale) := by
  have hn : Tendsto
      (fun N => ‖finiteComplexOrdinaryResolvent scale N -
        chosenComplexOrdinaryResolventCLM scale‖)
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero (fun N => norm_nonneg _) (fun N => ?_)
      complexOrdinaryResolventTailBound_tendsto
    simpa only [norm_sub_rev] using
      complexOrdinaryResolvent_finite_norm_bound scale N
  have hlim : Tendsto (finiteComplexOrdinaryResolvent scale)
      atTop (𝓝 (chosenComplexOrdinaryResolventCLM scale)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hn
  exact isCompactOperator_of_tendsto hlim
    (Filter.Eventually.of_forall
      (finiteComplexOrdinaryResolvent_compact scale))

end Neoplatonic.LTR
