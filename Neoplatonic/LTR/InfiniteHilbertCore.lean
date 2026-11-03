import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Lp.lpSpace

/-!
# Dense finite-coordinate core of the infinite Hilbert direct sum

The real infinite Dirac construction acts naturally on the Hilbert space
ℓ²(ℕ × Fin 2, ℝ). Its algebraic core consists of vectors supported on
finitely many coordinates. We use mathlib's actual l² and its theorem
that the finite-coordinate expansion of any vector has sum equal to
the original vector.

This file proves norm approximation by a finite-coordinate truncation,
a concrete density statement required for a densely defined operator.
It does not prove that the unbounded block operator is closed or
self-adjoint on its maximal graph domain.
-/

namespace Neoplatonic.LTR

open Filter
open scoped Topology lp

/-- A separable real Hilbert space with one 2-vector for each block. -/
abbrev InfiniteDiracHilbert := lp (fun _ : ℕ × Fin 2 => ℝ) 2

/-- Finite-coordinate truncations of an actual Hilbert vector. -/
noncomputable def finiteHilbertTruncation
    (ψ : InfiniteDiracHilbert) (s : Finset (ℕ × Fin 2)) :
    InfiniteDiracHilbert :=
  ∑ i ∈ s, lp.single 2 i (ψ i)

/-- Each truncation vanishes outside its chosen finite coordinate set. -/
theorem finiteHilbertTruncation_apply_of_not_mem
    (ψ : InfiniteDiracHilbert) (s : Finset (ℕ × Fin 2))
    (i : ℕ × Fin 2) (hi : i ∉ s) :
    finiteHilbertTruncation ψ s i = 0 := by
  change (∑ j ∈ s, Pi.single j (ψ j) i) = 0
  apply Finset.sum_eq_zero
  intro j hj
  have hji : j ≠ i := by
    intro heq
    exact hi (heq ▸ hj)
  exact Pi.single_eq_of_ne' hji _

/-- Every vector in the infinite Dirac Hilbert space can be approximated
arbitrarily closely by one with explicitly finite coordinate support. -/
theorem finiteHilbertTruncation_approx
    (ψ : InfiniteDiracHilbert) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset (ℕ × Fin 2),
      ‖ψ - finiteHilbertTruncation ψ s‖ < ε := by
  have hsum : HasSum
      (fun i : ℕ × Fin 2 => lp.single 2 i (ψ i)) ψ :=
    lp.hasSum_single (p := (2 : ENNReal))
      (by norm_num) ψ
  have hlim : Tendsto
      (fun s : Finset (ℕ × Fin 2) =>
        ∑ i ∈ s, lp.single 2 i (ψ i))
      atTop (𝓝 ψ) := hsum
  obtain ⟨s, hs⟩ :=
    (hlim.eventually (Metric.ball_mem_nhds ψ hε)).exists
  refine ⟨s, ?_⟩
  have hb : dist (∑ i ∈ s, lp.single 2 i (ψ i)) ψ < ε := by
    simpa only [Metric.mem_ball] using hs
  simpa only [finiteHilbertTruncation, dist_eq_norm, norm_sub_rev] using hb

end Neoplatonic.LTR
