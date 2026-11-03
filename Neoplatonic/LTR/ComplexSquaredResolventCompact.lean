import Neoplatonic.LTR.ComplexDiracSelfAdjoint
import Neoplatonic.LTR.InfiniteFiniteRank
import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension

/-!
# Compact squared-resolvent candidate on the complex Hilbert direct sum

The bounded operator R_C on ℓ²(ℕ, ℂ²) has scalar two-block weights
 w_j = (1 + 4^j + s_j²)⁻¹.
Finite-rank truncations are compact. Their operator-norm error is
bounded by 1 / (1+4^N), giving compactness on the infinite space.

The separate inverse identities will identify this compact map with
(I+D_C²)⁻¹ for the maximal self-adjoint complex Dirac operator.
-/

namespace Neoplatonic.LTR

open Filter
open scoped lp Topology

/-- A real scalar acts as a complex-linear continuous Euclidean map. -/
noncomputable def complexScalarBlockCLM (w : ℝ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (w : ℂ) • ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2))

/-- Complex Euclidean scalar multiplication has operator norm ≤ |w|. -/
theorem complexScalarBlockCLM_norm_le (w : ℝ) :
    ‖complexScalarBlockCLM w‖ ≤ |w| := by
  have h := norm_smul_le (w : ℂ)
    (ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2)))
  have hid : ‖ContinuousLinearMap.id ℂ
      (EuclideanSpace ℂ (Fin 2))‖ ≤ 1 :=
    ContinuousLinearMap.norm_id_le
  calc
    ‖complexScalarBlockCLM w‖ ≤ ‖(w : ℂ)‖ *
        ‖ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 2))‖ := h
    _ ≤ ‖(w : ℂ)‖ * 1 := mul_le_mul_of_nonneg_left hid (norm_nonneg _)
    _ = |w| := by simp

/-- A scalar diagonal bounded complex-linear Hilbert operator. -/
noncomputable def complexBoundedBlockDiagonal
    (w : ℕ → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hw : ∀ j, |w j| ≤ K) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  lp.mapCLM 2 (fun j => complexScalarBlockCLM (w j)) hK
    (fun j => (complexScalarBlockCLM_norm_le (w j)).trans (hw j))

/-- Operator-norm estimate from a uniform scalar-coefficient bound. -/
theorem complexBoundedBlockDiagonal_norm_le
    (w : ℕ → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hw : ∀ j, |w j| ≤ K) :
    ‖complexBoundedBlockDiagonal w K hK hw‖ ≤ K := by
  exact lp.norm_mapCLM_le 2 (fun j => complexScalarBlockCLM (w j)) hK
    (fun j => (complexScalarBlockCLM_norm_le (w j)).trans (hw j))

/-- Coordinate formula for the scalar complex diagonal Hilbert operator. -/
theorem complexBoundedBlockDiagonal_apply
    (w : ℕ → ℝ) (K : ℝ)
    (hK : 0 ≤ K) (hw : ∀ j, |w j| ≤ K)
    (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    complexBoundedBlockDiagonal w K hK hw ψ j = (w j : ℂ) • ψ j := by
  change complexScalarBlockCLM (w j) (ψ j) = (w j : ℂ) • ψ j
  simp [complexScalarBlockCLM]

/-- Complex Hilbert squared-resolvent operator with geometric weights. -/
noncomputable def chosenComplexSquaredResolventCLM
    (scale : ℕ → ℝ) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  complexBoundedBlockDiagonal (chosenSquaredResolventWeight scale) 1
    (by norm_num)
    (by
      intro j
      rw [abs_of_nonneg (chosenSquaredResolventWeight_nonneg scale j)]
      exact (chosenSquaredResolventWeight_le_tail scale j).trans
        (by
          unfold squaredResolventTail
          have hbase : (1 : ℝ) ≤ 1 + (4 : ℝ)^j := by
            have hp : 0 ≤ (4 : ℝ)^j := pow_nonneg (by norm_num) j
            linarith
          have hle := one_div_le_one_div_of_le
            (by norm_num : (0 : ℝ) < 1) hbase
          simpa [one_div] using hle))

/-- Every complex coordinate of the chosen squared resolvent. -/
theorem chosenComplexSquaredResolventCLM_apply
    (scale : ℕ → ℝ) (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    chosenComplexSquaredResolventCLM scale ψ j =
      ((chosenSquaredResolventWeight scale j : ℝ) : ℂ) • ψ j := by
  exact complexBoundedBlockDiagonal_apply _ _ _ _ ψ j

/-- The tail of the complex squared-resolvent diagonal. -/
noncomputable def chosenComplexSquaredResolventTailCLM
    (scale : ℕ → ℝ) (N : ℕ) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  complexBoundedBlockDiagonal
    (chosenSquaredResolventTailWeight scale N)
    (squaredResolventTail N)
    (squaredResolventTail_nonneg N)
    (chosenSquaredResolventTailWeight_abs_le scale N)

/-- Norm of the complex squared-resolvent tail decays geometrically. -/
theorem chosenComplexSquaredResolventTailCLM_norm_le
    (scale : ℕ → ℝ) (N : ℕ) :
    ‖chosenComplexSquaredResolventTailCLM scale N‖ ≤
      squaredResolventTail N :=
  complexBoundedBlockDiagonal_norm_le _ _ _ _

/-- Coordinate formula for the complex squared-resolvent tail. -/
theorem chosenComplexSquaredResolventTailCLM_apply
    (scale : ℕ → ℝ) (N : ℕ)
    (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    chosenComplexSquaredResolventTailCLM scale N ψ j =
      ((chosenSquaredResolventTailWeight scale N j : ℝ) : ℂ) • ψ j := by
  exact complexBoundedBlockDiagonal_apply _ _ _ _ ψ j

/-- A single complex squared-resolvent block, factored through ℂ². -/
noncomputable def complexSingleSquaredResolventBlock
    (scale : ℕ → ℝ) (j : ℕ) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  ((lp.singleContinuousLinearMap ℂ
      (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j).comp
        (complexScalarBlockCLM (chosenSquaredResolventWeight scale j))).comp
    (lp.evalCLM ℂ (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j)

/-- A single-block complex map is compact (finite-dimensional image). -/
theorem complexSingleSquaredResolventBlock_compact
    (scale : ℕ → ℝ) (j : ℕ) :
    IsCompactOperator (complexSingleSquaredResolventBlock scale j) := by
  have hev : IsCompactOperator
      (lp.evalCLM ℂ (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  unfold complexSingleSquaredResolventBlock
  exact hev.clm_comp
    ((lp.singleContinuousLinearMap ℂ
      (fun _ : ℕ => EuclideanSpace ℂ (Fin 2)) 2 j).comp
        (complexScalarBlockCLM (chosenSquaredResolventWeight scale j)))

/-- The sum of the first N finite-dimensional complex blocks. -/
noncomputable def finiteComplexSquaredResolvent
    (scale : ℕ → ℝ) (N : ℕ) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  ∑ j ∈ Finset.range N, complexSingleSquaredResolventBlock scale j

/-- Every finite truncation is a compact complex-linear operator. -/
theorem finiteComplexSquaredResolvent_compact
    (scale : ℕ → ℝ) (N : ℕ) :
    IsCompactOperator (finiteComplexSquaredResolvent scale N) := by
  classical
  unfold finiteComplexSquaredResolvent
  induction Finset.range N using Finset.induction_on with
  | empty =>
      simpa using
        (isCompactOperator_zero
          (M₁ := ComplexDiracBlockHilbert) (M₂ := ComplexDiracBlockHilbert))
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj]
      exact (complexSingleSquaredResolventBlock_compact scale j).add ih

/-- Coordinate formula for the finite complex block sum. -/
theorem finiteComplexSquaredResolvent_apply
    (scale : ℕ → ℝ) (N : ℕ)
    (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    (finiteComplexSquaredResolvent scale N ψ) j =
      if j < N then
        ((chosenSquaredResolventWeight scale j : ℝ) : ℂ) • ψ j
      else 0 := by
  classical
  have hsum :
      finiteComplexSquaredResolvent scale N ψ =
      ∑ i ∈ Finset.range N,
        lp.single 2 i
          (((chosenSquaredResolventWeight scale i : ℝ) : ℂ) • ψ i) := by
    simp [finiteComplexSquaredResolvent, complexSingleSquaredResolventBlock,
      complexScalarBlockCLM, lp.evalCLM, lp.evalₗ] <;> rfl
  rw [hsum]
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single]
  simp [Finset.sum_pi_single, Finset.mem_range]

/-- Exact identity: finite sum equals full complex R minus its tail. -/
theorem finiteComplexSquaredResolvent_eq_cutoff
    (scale : ℕ → ℝ) (N : ℕ) :
    finiteComplexSquaredResolvent scale N =
      chosenComplexSquaredResolventCLM scale -
        chosenComplexSquaredResolventTailCLM scale N := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext j
  rw [ContinuousLinearMap.sub_apply, lp.coeFn_sub, Pi.sub_apply,
    chosenComplexSquaredResolventCLM_apply,
    chosenComplexSquaredResolventTailCLM_apply,
    finiteComplexSquaredResolvent_apply]
  by_cases hj : j < N
  · have hn : ¬ N ≤ j := by omega
    simp [chosenSquaredResolventTailWeight, hn, hj]
  · have hn : N ≤ j := Nat.le_of_not_gt hj
    simp [chosenSquaredResolventTailWeight, hn, hj]

/-- Operator-norm truncation error bounded by the geometric tail. -/
theorem complexSquaredResolvent_finite_norm_bound
    (scale : ℕ → ℝ) (N : ℕ) :
    ‖chosenComplexSquaredResolventCLM scale -
       finiteComplexSquaredResolvent scale N‖ ≤ squaredResolventTail N := by
  rw [finiteComplexSquaredResolvent_eq_cutoff]
  convert chosenComplexSquaredResolventTailCLM_norm_le scale N using 1
  congr 1
  abel

/-- Compactness of the actual complex Hilbert squared-resolvent candidate. -/
theorem chosenComplexSquaredResolvent_isCompact
    (scale : ℕ → ℝ) :
    IsCompactOperator (chosenComplexSquaredResolventCLM scale) := by
  have hn : Tendsto
      (fun N => ‖finiteComplexSquaredResolvent scale N -
        chosenComplexSquaredResolventCLM scale‖)
      atTop (nhds (0 : ℝ)) := by
    apply squeeze_zero (fun N => norm_nonneg _) (fun N => ?_)
      squaredResolventTail_tendsto
    simpa only [norm_sub_rev] using
      complexSquaredResolvent_finite_norm_bound scale N
  have hlim : Tendsto (finiteComplexSquaredResolvent scale)
      atTop (nhds (chosenComplexSquaredResolventCLM scale)) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr hn
  exact isCompactOperator_of_tendsto hlim
    (Filter.Eventually.of_forall (finiteComplexSquaredResolvent_compact scale))

end Neoplatonic.LTR
