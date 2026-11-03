import Neoplatonic.LTR.InfiniteFiniteRank

/-!
# Compact squared resolvent for a concrete infinite Hilbert operator

The full diagonal squared-resolvent operator has coordinate weights
w_j = (1+4^j+s_j²)^(-1). Its first-N-block cutoff is an actual finite
sum of compact rank-two operators. This module proves the equality
between the cutoff and the complement of the resolvent's tail, obtains
the exact operator norm error bound, then applies mathlib's
norm-closed compact-operator theorem.

This is an actual compact operator on the full infinite-dimensional
Hilbert space. Identification with (I+D²)^(-1) for a *closed unbounded*
D requires the separate maximal-domain and self-adjointness proof.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Evaluation of a single rank-two block insertion. -/
theorem singleSquaredResolventBlock_apply
    (scale : ℕ → ℝ) (i : ℕ)
    (ψ : DiracBlockHilbert) (j : ℕ) :
    (singleSquaredResolventBlock scale i ψ) j =
      ((lp.single (E := fun _ : ℕ => EuclideanSpace ℝ (Fin 2))
          2 i (chosenSquaredResolventWeight scale i • ψ i)) :
          DiracBlockHilbert) j := by
  simp [singleSquaredResolventBlock, scalarBlockCLM,
    lp.evalCLM, lp.evalₗ]

/-- The finite sum of compact block operators is the first-N cutoff. -/
theorem finiteSquaredResolvent_apply
    (scale : ℕ → ℝ) (N : ℕ)
    (ψ : DiracBlockHilbert) (j : ℕ) :
    (finiteSquaredResolvent scale N ψ) j =
      if j < N then chosenSquaredResolventWeight scale j • ψ j
        else 0 := by
  classical
  have hsum :
      finiteSquaredResolvent scale N ψ =
        ∑ i ∈ Finset.range N,
          lp.single 2 i
            (chosenSquaredResolventWeight scale i • ψ i) := by
    simp [finiteSquaredResolvent, singleSquaredResolventBlock,
      scalarBlockCLM]
  rw [hsum]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
  simp [Finset.sum_pi_single, Finset.mem_range]

/-- The explicit finite-rank cutoff agrees with R minus the tail. -/
theorem finiteSquaredResolvent_eq_cutoff
    (scale : ℕ → ℝ) (N : ℕ) :
    finiteSquaredResolvent scale N =
      chosenSquaredResolventCLM scale -
        chosenSquaredResolventTailCLM scale N := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  exact (finiteSquaredResolvent_apply scale N ψ j).trans
    (squaredResolventCutoff_apply scale N ψ j).symm

/-- Error from truncating at N blocks is exactly the tail operator. -/
theorem squaredResolvent_sub_finite_eq_tail
    (scale : ℕ → ℝ) (N : ℕ) :
    chosenSquaredResolventCLM scale -
      finiteSquaredResolvent scale N =
      chosenSquaredResolventTailCLM scale N := by
  rw [finiteSquaredResolvent_eq_cutoff]
  abel

/-- The concrete infinite squared resolvent has an explicit
exponentially decaying finite-rank approximation error. -/
theorem squaredResolvent_finite_norm_bound
    (scale : ℕ → ℝ) (N : ℕ) :
    ‖chosenSquaredResolventCLM scale -
       finiteSquaredResolvent scale N‖ ≤
      squaredResolventTail N := by
  rw [squaredResolvent_sub_finite_eq_tail]
  exact chosenSquaredResolventTailCLM_norm_le scale N

/-- Actual compactness of the bounded squared-resolvent operator
on the full infinite real Hilbert space, from finite-rank cutoffs. -/
theorem chosenSquaredResolvent_isCompact
    (scale : ℕ → ℝ) :
    IsCompactOperator (chosenSquaredResolventCLM scale) := by
  apply compact_of_squaredResolvent_tail
    (chosenSquaredResolventCLM scale)
    (finiteSquaredResolvent scale)
  · intro N
    exact finiteSquaredResolvent_compact scale N
  · intro N
    exact squaredResolvent_finite_norm_bound scale N

end Neoplatonic.LTR
