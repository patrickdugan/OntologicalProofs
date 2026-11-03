import Neoplatonic.LTR.ComplexObservableCommutator

/-!
# Exact marked-edge commutator seminorm

The bounded global commutator C on ℓ²(ℕ,ℂ²) has blocks
C_j=[D_j, diag(left_j,right_j)].
The operator norm dominates the exact norm of every individual
two-point commutator block. Combined with the uniform upper bound,
this makes the global commutator norm the least uniform bound for
the marked edge quotients |scale_j*(right_j-left_j)|.

The strong exact norm characterization is stated without introducing
a convention for an empty or unbounded supremum.
-/

namespace Neoplatonic.LTR

open scoped lp

set_option maxHeartbeats 2000000 in
/-- Any bounded complex Hilbert operator acting coordinatewise
dominates each of its block operator norms. The Hilbert operator
is a parameter, avoiding dependent reduction of lp.mapCLM. -/
theorem complexHilbertBlock_norm_le_operator
    (T : ℕ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
    (F : ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert)
    (hcoord : ∀ ψ : ComplexDiracBlockHilbert, ∀ j : ℕ,
      (F ψ) j = T j (ψ j))
    (j : ℕ) :
    ‖T j‖ ≤ ‖F‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg F)
  intro v
  have hsingle : (F (lp.single 2 j v)) j = T j v := by
    rw [hcoord]
    simp
  have hp : (2 : ENNReal) ≠ 0 := by norm_num
  have hp_pos : 0 < (2 : ENNReal) := by norm_num
  calc
    ‖T j v‖ = ‖(F (lp.single 2 j v)) j‖ := by rw [hsingle]
    _ ≤ ‖F (lp.single 2 j v)‖ :=
      lp.norm_apply_le_norm hp (F (lp.single 2 j v)) j
    _ ≤ ‖F‖ * ‖lp.single 2 j v‖ := F.le_opNorm _
    _ = ‖F‖ * ‖v‖ := by rw [lp.norm_single hp_pos]

/-- Any individual marked-edge commutator norm is bounded above
by the norm of the global bounded Hilbert commutator. -/
theorem complexPairCommutatorBlock_norm_le_global
    (mass scale left right : ℕ → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hEdge : ∀ j, |scale j * (right j - left j)| ≤ L)
    (j : ℕ) :
    ‖complexPairCommutatorBlock mass scale left right j‖ ≤
      ‖complexPairCommutatorCLM mass scale left right L hL hEdge‖ := by
  exact complexHilbertBlock_norm_le_operator
    (complexPairCommutatorBlock mass scale left right)
    (complexPairCommutatorCLM mass scale left right L hL hEdge)
    (complexPairCommutatorCLM_apply mass scale left right L hL hEdge)
    j

/-- Every edge Lipschitz quotient is at most the global commutator norm. -/
theorem complexPairCommutator_edge_le_norm
    (mass scale left right : ℕ → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hEdge : ∀ j, |scale j * (right j - left j)| ≤ L)
    (j : ℕ) :
    |scale j * (right j - left j)| ≤
      ‖complexPairCommutatorCLM mass scale left right L hL hEdge‖ := by
  rw [← complexPairCommutatorBlock_norm]
  exact complexPairCommutatorBlock_norm_le_global
    mass scale left right L hL hEdge j

/-- The global commutator is independent of which valid norm cap was
used to construct its continuous linear map. -/
theorem complexPairCommutatorCLM_eq_of_bounds
    (mass scale left right : ℕ → ℝ)
    (L M : ℝ) (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hEdgeL : ∀ j, |scale j * (right j - left j)| ≤ L)
    (hEdgeM : ∀ j, |scale j * (right j - left j)| ≤ M) :
    complexPairCommutatorCLM mass scale left right L hL hEdgeL =
      complexPairCommutatorCLM mass scale left right M hM hEdgeM := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  rw [complexPairCommutatorCLM_apply, complexPairCommutatorCLM_apply]

/-- The norm of the bounded global commutator is the optimal uniform
upper bound for all marked edge Lipschitz quotients. -/
theorem complexPairCommutator_norm_le_iff
    (mass scale left right : ℕ → ℝ)
    (L M : ℝ) (hL : 0 ≤ L)
    (hEdgeL : ∀ j, |scale j * (right j - left j)| ≤ L)
    (hM : 0 ≤ M) :
    ‖complexPairCommutatorCLM mass scale left right L hL hEdgeL‖ ≤ M ↔
      ∀ j, |scale j * (right j - left j)| ≤ M := by
  constructor
  · intro h j
    exact (complexPairCommutator_edge_le_norm
      mass scale left right L hL hEdgeL j).trans h
  · intro h
    rw [complexPairCommutatorCLM_eq_of_bounds
      mass scale left right L M hL hM hEdgeL h]
    exact complexPairCommutatorCLM_norm_le
      mass scale left right M hM h

end Neoplatonic.LTR
