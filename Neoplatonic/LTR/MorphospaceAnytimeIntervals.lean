import Neoplatonic.LTR.MorphospaceSquareCover
import Mathlib

/-!
# MOR-07: a rational interval Chebyshev certificate for adaptive quotients

This formalizes the deterministic interval geometry in QO-07.
No stochastic martingale or Ville inequality is asserted here. Those
remain explicitly established mathematical premises of the external
confidence-sequence protocol.

The interpretation of q as a fitted macrostate hit probability, and
of p as a true microscopic hit rate, is a declared model contract.
-/

namespace Neoplatonic.LTR.Morphospace

/-- A rational hit probability within a declared inclusive interval. -/
def RateInInterval (lo hi p : ℚ) : Prop := lo ≤ p ∧ p ≤ hi

/-- Center of the smallest interval containing all candidate rates. -/
def intervalMidpoint (lo hi : ℚ) : ℚ := (lo + hi) / 2

/-- The minimax absolute error over a rational interval. -/
def intervalHalfWidth (lo hi : ℚ) : ℚ := (hi - lo) / 2

/-- The interval midpoint predicts any admissible probability within
half the span of the bounding interval. -/
theorem interval_midpoint_error_le
    (lo hi p : ℚ) (hp : RateInInterval lo hi p) :
    |p - intervalMidpoint lo hi| ≤ intervalHalfWidth lo hi := by
  rcases hp with ⟨hlo, hhi⟩
  apply abs_le.mpr
  constructor
  · dsimp [intervalMidpoint, intervalHalfWidth]
    linarith
  · dsimp [intervalMidpoint, intervalHalfWidth]
    linarith

/-- Every competing predictor has error at least half the interval
width on one of the two endpoints. -/
theorem interval_midpoint_minimax_lower
    (lo hi q : ℚ) (h : lo ≤ hi) :
    intervalHalfWidth lo hi ≤ max (|lo - q|) (|hi - q|) := by
  have htriangle : |hi - lo| ≤ |hi - q| + |q - lo| :=
    abs_sub_le hi q lo
  have habs : |hi - lo| = hi - lo :=
    abs_of_nonneg (sub_nonneg.mpr h)
  rw [habs, abs_sub_comm q lo] at htriangle
  have hleft : |lo - q| ≤ max (|lo - q|) (|hi - q|) :=
    le_max_left _ _
  have hright : |hi - q| ≤ max (|lo - q|) (|hi - q|) :=
    le_max_right _ _
  dsimp [intervalHalfWidth]
  linarith

/-- Rational midpoint is a complete minimax certificate: an achievable
uniform error bound and a matching lower bound on every candidate center. -/
theorem interval_chebyshev_optimal
    (lo hi : ℚ) (h : lo ≤ hi) :
    (∀ p, RateInInterval lo hi p →
      |p - intervalMidpoint lo hi| ≤ intervalHalfWidth lo hi) ∧
    (∀ q, intervalHalfWidth lo hi ≤ max (|lo - q|) (|hi - q|)) := by
  constructor
  · intro p hp
    exact interval_midpoint_error_le lo hi p hp
  · intro q
    exact interval_midpoint_minimax_lower lo hi q h

/-- Intersecting two separately valid intervals remains valid. This is
the deterministic step used when nesting e-process confidence sets. -/
theorem nested_interval_contains
    (p lo₁ hi₁ lo₂ hi₂ : ℚ)
    (h₁ : RateInInterval lo₁ hi₁ p)
    (h₂ : RateInInterval lo₂ hi₂ p) :
    RateInInterval (max lo₁ lo₂) (min hi₁ hi₂) p := by
  rcases h₁ with ⟨hl₁, hu₁⟩
  rcases h₂ with ⟨hl₂, hu₂⟩
  constructor
  · exact max_le hl₁ hl₂
  · exact le_min hu₁ hu₂

/-- One wholly unobserved Bernoulli parameter in [0,1] cannot have
a uniform absolute prediction error smaller than 1/2. -/
theorem unprobed_cell_half_error_lower (q : ℚ) :
    (1 / 2 : ℚ) ≤ max (|q|) (|1 - q|) := by
  have h := interval_midpoint_minimax_lower (0 : ℚ) 1 q (by norm_num)
  simpa [intervalHalfWidth] using h

/-- Given an observed lower bound for p and upper bound for q, their
positive gap is a certified lower bound on the true separation. -/
theorem optimistic_pair_gap
    (lo upper p q : ℚ)
    (hp : lo ≤ p) (hq : q ≤ upper) :
    max (0 : ℚ) (lo - upper) ≤ |p - q| := by
  apply max_le
  · exact abs_nonneg _
  · have hpq : p - q ≤ |p - q| := le_abs_self _
    linarith

end Neoplatonic.LTR.Morphospace
