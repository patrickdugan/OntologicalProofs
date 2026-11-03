import Neoplatonic.LTR.BoundedHilbertDiagonal
import Mathlib.Analysis.InnerProductSpace.l2Space

/-!
# Density of the actual two-component Hilbert-block core

The earlier flattened ℓ²(ℕ×Fin 2,ℝ) approximation is mirrored here for
the exact Dirac Hilbert space H = ℓ²(ℕ, EuclideanSpace ℝ (Fin 2)).
The union of finite-block coordinate subspaces is norm-dense in H.

These vectors are precisely the algebraic core on which the growing
mass-shifted Dirac blocks act. Density is a necessary first step toward
an unbounded self-adjoint operator; it is not itself a closedness proof.
-/

namespace Neoplatonic.LTR

open Filter
open scoped Topology lp

/-- Finite-block truncation in the exact infinite Dirac Hilbert sum. -/
noncomputable def finiteBlockTruncation
    (ψ : DiracBlockHilbert) (s : Finset ℕ) : DiracBlockHilbert :=
  ∑ j ∈ s, lp.single 2 j (ψ j)

/-- Finite block truncation has zero coordinates outside its support. -/
theorem finiteBlockTruncation_apply_of_not_mem
    (ψ : DiracBlockHilbert) (s : Finset ℕ)
    (j : ℕ) (hj : j ∉ s) :
    finiteBlockTruncation ψ s j = 0 := by
  simp only [finiteBlockTruncation, lp.coeFn_sum,
    Finset.sum_apply, lp.coeFn_single]
  apply Finset.sum_eq_zero
  intro i hi
  have hij : i ≠ j := by
    intro heq
    exact hj (heq ▸ hi)
  exact Pi.single_eq_of_ne' hij _

/-- Every Hilbert vector can be approximated in norm by finitely many
two-component blocks. This is the core-density theorem for this H. -/
theorem finiteBlockTruncation_approx
    (ψ : DiracBlockHilbert) (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset ℕ, ‖ψ - finiteBlockTruncation ψ s‖ < ε := by
  have hsum :
      HasSum (fun j : ℕ => lp.single 2 j (ψ j)) ψ :=
    lp.hasSum_single (p := (2 : ENNReal)) (by norm_num) ψ
  have hlim : Tendsto
      (fun s : Finset ℕ => ∑ j ∈ s, lp.single 2 j (ψ j))
      atTop (𝓝 ψ) := hsum
  obtain ⟨s, hs⟩ :=
    (hlim.eventually (Metric.ball_mem_nhds ψ hε)).exists
  refine ⟨s, ?_⟩
  have hb : dist (∑ j ∈ s, lp.single 2 j (ψ j)) ψ < ε := by
    simpa only [Metric.mem_ball] using hs
  simpa only [finiteBlockTruncation, dist_eq_norm, norm_sub_rev] using hb

end Neoplatonic.LTR
