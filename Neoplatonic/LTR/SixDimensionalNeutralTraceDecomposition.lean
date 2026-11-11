import Neoplatonic.LTR.SixDimensionalExactHammingAmbientInvolution
import Mathlib.Tactic

/-!
# LTR-MAN-92: neutral-fibre decomposition of the square trace

For a finite complex matrix W, let N be a subset of coordinate
indices on which the N-to-N matrix block is zero. Since
trace(W²) = ∑ᵢⱼ Wᵢⱼ Wⱼᵢ, splitting ordered pairs by whether
either end lies in N gives the exact algebraic identity

  trace(W²) =
      2 ∑ᵢ∈N (W²)ᵢᵢ + ∑ᵢ∉N,ⱼ∉N Wᵢⱼ Wⱼᵢ.

The two cross terms agree by swapping i,j, without any Hermiticity
hypothesis. At W²=I₆ the neutral-fibre row sum is simply |N|.

The following lemmas prepare the rank-sensitive MAN-92 trace
obstruction for the original six-dimensional labelled Dirac
commutators, without assuming abstract support or Gram properties.
-/

namespace Neoplatonic.LTR

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Finite trace decomposition for a matrix whose neutral-neutral
quadratic products vanish. No self-adjointness is required. -/
theorem sixMatrix_trace_square_neutral_decomposition
    (W : SixMat) (neutral : Fin 6 → Prop)
    [DecidablePred neutral]
    (hNN : ∀ i j : Fin 6, neutral i → neutral j →
      W i j * W j i = 0) :
    (W * W).trace =
      (2 : ℂ) * (∑ i : Fin 6,
        if neutral i then (W * W) i i else 0) +
      ∑ i : Fin 6, ∑ j : Fin 6,
        if ¬neutral i ∧ ¬neutral j then W i j * W j i else 0 := by
  classical
  have hpoint (i j : Fin 6) :
      W i j * W j i =
        (if neutral i then W i j * W j i else 0) +
        (if neutral j then W i j * W j i else 0) +
        (if ¬neutral i ∧ ¬neutral j then W i j * W j i else 0) := by
    by_cases hi : neutral i <;> by_cases hj : neutral j
    · simp [hi, hj, hNN i j hi hj]
    · simp [hi, hj]
    · simp [hi, hj]
    · simp [hi, hj]
  have hsplit :
      (∑ i : Fin 6, ∑ j : Fin 6, W i j * W j i) =
        (∑ i : Fin 6, ∑ j : Fin 6,
          if neutral i then W i j * W j i else 0) +
        (∑ i : Fin 6, ∑ j : Fin 6,
          if neutral j then W i j * W j i else 0) +
        (∑ i : Fin 6, ∑ j : Fin 6,
          if ¬neutral i ∧ ¬neutral j then W i j * W j i else 0) := by
    calc
      _ = ∑ i : Fin 6, ∑ j : Fin 6,
          ((if neutral i then W i j * W j i else 0) +
           (if neutral j then W i j * W j i else 0) +
           (if ¬neutral i ∧ ¬neutral j then W i j * W j i else 0)) := by
          apply Finset.sum_congr rfl
          intro i hi
          apply Finset.sum_congr rfl
          intro j hj
          exact hpoint i j
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hswap :
      (∑ i : Fin 6, ∑ j : Fin 6,
        if neutral j then W i j * W j i else 0) =
      (∑ i : Fin 6, ∑ j : Fin 6,
        if neutral i then W i j * W j i else 0) := by
    calc
      _ = ∑ j : Fin 6, ∑ i : Fin 6,
        if neutral j then W i j * W j i else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hn : neutral i <;> simp [hn, mul_comm]
  have hrow :
      (∑ i : Fin 6, ∑ j : Fin 6,
        if neutral i then W i j * W j i else 0) =
      (∑ i : Fin 6, if neutral i then (W * W) i i else 0) := by
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hn : neutral i <;> simp [hn, Matrix.mul_apply]
  calc
    (W * W).trace = (∑ i : Fin 6, ∑ j : Fin 6,
        W i j * W j i) := by rfl
    _ = _ := hsplit
    _ = (2 : ℂ) * (∑ i : Fin 6,
          if neutral i then (W * W) i i else 0) +
        ∑ i : Fin 6, ∑ j : Fin 6,
          if ¬neutral i ∧ ¬neutral j then W i j * W j i else 0 := by
      rw [hswap, hrow]
      ring

/-- If the neutral-neutral block vanishes and the six-dimensional
matrix is an involution, the complementary ordered quadratic sum
is determined by the cardinality of the neutral subset. -/
theorem sixMatrix_involution_neutral_card_budget
    (W : SixMat) (neutral : Fin 6 → Prop)
    [DecidablePred neutral]
    (hNN : ∀ i j : Fin 6, neutral i → neutral j →
      W i j * W j i = 0)
    (hW : W * W = 1) :
    (6 : ℂ) =
      (2 : ℂ) * ((Finset.univ.filter neutral).card : ℂ) +
      ∑ i : Fin 6, ∑ j : Fin 6,
        if ¬neutral i ∧ ¬neutral j then W i j * W j i else 0 := by
  classical
  have ht := sixMatrix_trace_square_neutral_decomposition W neutral hNN
  rw [hW] at ht
  have honeTrace : (1 : SixMat).trace = (6 : ℂ) := by
    norm_num [Matrix.trace, Matrix.diag, Fin.sum_univ_six]
  have hneutralCard :
      (∑ i : Fin 6, if neutral i then (1 : SixMat) i i else 0) =
        ((Finset.univ.filter neutral).card : ℂ) := by
    simp [Matrix.one_apply, Finset.sum_ite, Finset.sum_const,
      nsmul_eq_mul]
  rw [honeTrace, hneutralCard] at ht
  exact ht

end Neoplatonic.LTR
