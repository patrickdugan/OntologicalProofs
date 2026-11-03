import Mathlib

/-!
# The metric / observable bridge and exact Dirac block algebra

The first theorem identifies a map's metric bound by its action on all
real 1-Lipschitz observables. In a spectral realization with commutator
seminorm equal to the Lipschitz seminorm, this is the exact optimal pullback
bound. That analytic realization is proved in the companion written note,
using the Christensen--Ivan construction; it is not an axiom in this file.

The matrix results check the finite algebra behind that construction.
Self-adjointness of the infinite direct sum and compactness of its resolvent
remain written analytic proofs, explicitly separate from these identities.
-/

namespace Neoplatonic.LTR

universe u v

/-- Testing all real 1-Lipschitz observables recovers exactly the map's
metric bound. The distance-to-a-target function witnesses the converse. -/
theorem metric_bound_iff_observable_bound
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (C : ℝ) :
    (∀ x y, dist (f x) (f y) ≤ C * dist x y) ↔
    (∀ a : Y → ℝ,
      (∀ y z, |a y - a z| ≤ dist y z) →
      ∀ x y, |a (f x) - a (f y)| ≤ C * dist x y) := by
  constructor
  · intro hf a ha x y
    exact (ha _ _).trans (hf x y)
  · intro h x y
    have hdist : ∀ p q : Y,
        |dist p (f y) - dist q (f y)| ≤ dist p q := by
      intro p q
      exact abs_dist_sub_le p q (f y)
    have hv := h (fun z => dist z (f y)) hdist x y
    simpa only [dist_self, sub_zero, abs_of_nonneg dist_nonneg] using hv

/-- On a nonempty metric space the ordinary metric is exactly the supremum
of differences of real unit-Lipschitz observables, stated via upper bounds
and an attaining witness so no conditional-completeness convention is hidden. -/
theorem metric_recovery_witness
    {X : Type u} [MetricSpace X] (x y : X) :
    (∀ a : X → ℝ,
      (∀ p q, |a p - a q| ≤ dist p q) → |a x - a y| ≤ dist x y) ∧
    ∃ a : X → ℝ,
      (∀ p q, |a p - a q| ≤ dist p q) ∧ |a x - a y| = dist x y := by
  constructor
  · intro a ha
    exact ha x y
  · refine ⟨fun z => dist z y, ?_, ?_⟩
    · intro p q
      exact abs_dist_sub_le p q y
    · simp only [dist_self, sub_zero, abs_of_nonneg dist_nonneg]

/-- Contravariant observable pullback respects composition exactly. -/
theorem observable_pullback_comp
    {X : Type u} {Y : Type v} {Z : Type*}
    (f : X → Y) (g : Y → Z) (a : Z → ℝ) :
    (a ∘ g) ∘ f = a ∘ (g ∘ f) := rfl

/-- A mass-shifted two-point Dirac block, with off-diagonal inverse distance. -/
def massDirac (mass scale : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![mass, scale; scale, -mass]

/-- A diagonal observable evaluates a function at the two marked points. -/
def diagonalObservable (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a, 0; 0, b]

/-- The mass leaves the commutator unchanged. -/
theorem massDirac_commutator (mass scale a b : ℝ) :
    massDirac mass scale * diagonalObservable a b -
      diagonalObservable a b * massDirac mass scale =
    !![0, scale * (b - a); scale * (a - b), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [massDirac, diagonalObservable, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem massDirac_commutator_independent (m n scale a b : ℝ) :
    massDirac m scale * diagonalObservable a b -
      diagonalObservable a b * massDirac m scale =
    massDirac n scale * diagonalObservable a b -
      diagonalObservable a b * massDirac n scale := by
  rw [massDirac_commutator, massDirac_commutator]

/-- Squaring moves both eigenvalues away from zero without changing commutators. -/
theorem massDirac_square (mass scale : ℝ) :
    massDirac mass scale * massDirac mass scale =
      (mass^2 + scale^2) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [massDirac, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem massDirac_symmetric (mass scale : ℝ) :
    (massDirac mass scale).transpose = massDirac mass scale := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- Euclidean energy of the commutator action. This identity yields its
operator norm |scale|*|a-b| on the two-dimensional Euclidean space. -/
theorem commutator_energy (scale a b u v : ℝ) :
    (scale * (b - a) * v)^2 + (scale * (a - b) * u)^2 =
      (scale^2 * (a - b)^2) * (u^2 + v^2) := by
  ring

/-- A scalar estimate for the squared-resolvent tail. The infinite direct-sum
compactness deduction is supplied as a written proof in FILTERED_SPECTRAL.md. -/
theorem mass_resolvent_bound (mass scale lower : ℝ)
    (hl : 0 ≤ lower) (hm : lower ≤ mass) :
    1 / (1 + mass^2 + scale^2) ≤ 1 / (1 + lower^2) := by
  apply one_div_le_one_div_of_le
  · positivity
  · nlinarith [sq_nonneg scale, sq_nonneg (mass - lower)]

end Neoplatonic.LTR
