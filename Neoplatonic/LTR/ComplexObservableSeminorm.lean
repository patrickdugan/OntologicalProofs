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

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 1000000 in
/-- The norm of a coordinatewise bounded operator on a complex
ℓ² direct sum dominates the operator norm on each coordinate.
Use the norm-one evaluation and insertion maps to avoid large
dependent elaboration within the operator-norm proof. -/
theorem complexHilbertBlock_norm_le_operator
    (T : ℕ → EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2))
    (F : ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert)
    (hcoord : ∀ ψ : ComplexDiracBlockHilbert, ∀ j : ℕ,
      (F ψ) j = T j (ψ j))
    (j : ℕ) :
    ‖T j‖ ≤ ‖F‖ := by
  let E : ComplexDiracBlockHilbert →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
    lp.evalCLM ℂ (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j
  let S : EuclideanSpace ℂ (Fin 2) →L[ℂ] ComplexDiracBlockHilbert :=
    lp.singleContinuousLinearMap ℂ (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j
  have hcomp : T j = E.comp (F.comp S) := by
    apply ContinuousLinearMap.ext
    intro v
    change T j v = (F (lp.single 2 j v)) j
    rw [hcoord]
    simp
  have hEval : ‖E‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound E (by norm_num)
    intro ψ
    change ‖ψ j‖ ≤ 1 * ‖ψ‖
    simpa only [one_mul] using
      (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) ψ j)
  have hSingle : ‖S‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound S (by norm_num)
    intro v
    calc
      ‖S v‖ = ‖lp.single 2 j v‖ := by
        rw [show S v = lp.single 2 j v from
          lp.singleContinuousLinearMap_apply
            (𝕜 := ℂ) (E := fun _ : ℕ => EuclideanSpace ℂ (Fin 2))
            (p := 2) j v]
      _ = ‖v‖ := by
        exact lp.norm_single
          (E := fun _ : ℕ => EuclideanSpace ℂ (Fin 2))
          (p := (2 : ENNReal))
          (by norm_num : 0 < (2 : ENNReal)) j v
      _ ≤ 1 * ‖v‖ := by simp
  have hInner : ‖F.comp S‖ ≤ ‖F‖ := by
    calc
      ‖F.comp S‖ ≤ ‖F‖ * ‖S‖ :=
        ContinuousLinearMap.opNorm_comp_le F S
      _ ≤ ‖F‖ * 1 :=
        mul_le_mul_of_nonneg_left hSingle (norm_nonneg F)
      _ = ‖F‖ := mul_one _
  calc
    ‖T j‖ = ‖E.comp (F.comp S)‖ := congrArg norm hcomp
    _ ≤ ‖E‖ * ‖F.comp S‖ :=
      ContinuousLinearMap.opNorm_comp_le E (F.comp S)
    _ ≤ 1 * ‖F.comp S‖ :=
      mul_le_mul_of_nonneg_right hEval (norm_nonneg (F.comp S))
    _ = ‖F.comp S‖ := one_mul _
    _ ≤ ‖F‖ := hInner

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
