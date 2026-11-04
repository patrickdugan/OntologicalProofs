import Neoplatonic.LTR.BooleanCubeEdges
import Neoplatonic.LTR.ComplexObservableSeminorm

/-!
# LTR-MAN-09B: finite hypercube Hilbert Dirac and exact global gradient

The finite hypercube carries one actual complex Euclidean 2x2 Hilbert
block for each undirected edge. The global Hilbert space is the
ℓ² direct sum over the finite edge type, and D and π(f) act blockwise.

The commutator [D,π(f)] is the same block-diagonal operator as the
existing certified 2x2 local commutator. Its norm equals the maximum
edge gradient, including the zero-dimensional cube where there are no
edges and the maximum is defined as zero.

These are genuine bounded complex-linear Hilbert operators. The graph
distance reconstruction and enumeration of edge count are separate
obligations, addressed in the following modules.
-/

namespace Neoplatonic.LTR

open scoped lp

noncomputable section

/-- Genuine Hilbert ℓ² sum, with one two-dimensional complex block
per distinct undirected Boolean-hypercube edge. -/
abbrev BooleanCubeHilbert (m : ℕ) :=
  lp (fun _ : BooleanCubeEdge m => EuclideanSpace ℂ (Fin 2)) 2

/-- Finite maximum local observable norm. -/
noncomputable def booleanCubeObservableCap {m : ℕ}
    (f : BooleanCubeVertex m → ℂ) : NNReal := by
  classical
  exact (Finset.univ : Finset (BooleanCubeEdge m)).sup
    (fun e => ‖booleanCubeLocalObservable f e‖₊)

/-- Finite maximum local commutator norm. -/
noncomputable def booleanCubeGradientCap {m : ℕ}
    (f : BooleanCubeVertex m → ℂ) : NNReal := by
  classical
  exact (Finset.univ : Finset (BooleanCubeEdge m)).sup
    (fun e => ‖booleanCubeLocalCommutator f e‖₊)

/-- The actual bounded block Dirac operator, with mass zero,
unit coupling and self-adjoint local two-point matrices. -/
noncomputable def booleanCubeDirac (m : ℕ) :
    BooleanCubeHilbert m →L[ℂ] BooleanCubeHilbert m :=
  lp.mapCLM 2
    (fun _ : BooleanCubeEdge m => booleanCubeLocalDirac)
    (norm_nonneg booleanCubeLocalDirac)
    (by intro e; exact le_rfl)

/-- A bounded multiplication operator by the two endpoint values
of f on each hypercube edge. -/
noncomputable def booleanCubeObservable {m : ℕ}
    (f : BooleanCubeVertex m → ℂ) :
    BooleanCubeHilbert m →L[ℂ] BooleanCubeHilbert m :=
  lp.mapCLM 2 (booleanCubeLocalObservable f)
    (NNReal.coe_nonneg (booleanCubeObservableCap f))
    (by
      intro e
      have h : ‖booleanCubeLocalObservable f e‖₊ ≤
          booleanCubeObservableCap f := by
        unfold booleanCubeObservableCap
        exact Finset.le_sup (Finset.mem_univ e)
      exact_mod_cast h)

/-- The bounded finite-Hilbert direct sum of actual 2x2
commutator blocks. -/
noncomputable def booleanCubeCommutator {m : ℕ}
    (f : BooleanCubeVertex m → ℂ) :
    BooleanCubeHilbert m →L[ℂ] BooleanCubeHilbert m :=
  lp.mapCLM 2 (booleanCubeLocalCommutator f)
    (NNReal.coe_nonneg (booleanCubeGradientCap f))
    (by
      intro e
      have h : ‖booleanCubeLocalCommutator f e‖₊ ≤
          booleanCubeGradientCap f := by
        unfold booleanCubeGradientCap
        exact Finset.le_sup (Finset.mem_univ e)
      exact_mod_cast h)

/-- Exact coordinate formula for the cube Dirac. -/
theorem booleanCubeDirac_apply (m : ℕ)
    (ψ : BooleanCubeHilbert m) (e : BooleanCubeEdge m) :
    (booleanCubeDirac m ψ) e = booleanCubeLocalDirac (ψ e) := by
  rfl

/-- Exact coordinate formula for the observed truth operator. -/
theorem booleanCubeObservable_apply {m : ℕ}
    (f : BooleanCubeVertex m → ℂ)
    (ψ : BooleanCubeHilbert m) (e : BooleanCubeEdge m) :
    (booleanCubeObservable f ψ) e =
      booleanCubeLocalObservable f e (ψ e) := by
  rfl

/-- Coordinate formula for the genuinely bounded global commutator. -/
theorem booleanCubeCommutator_apply {m : ℕ}
    (f : BooleanCubeVertex m → ℂ)
    (ψ : BooleanCubeHilbert m) (e : BooleanCubeEdge m) :
    (booleanCubeCommutator f ψ) e =
      booleanCubeLocalCommutator f e (ψ e) := by
  rfl

/-- The previously defined global commutator is the actual operator
difference Dπ(f)-π(f)D on the finite Hilbert ℓ² direct sum. -/
theorem booleanCubeCommutator_eq_operator {m : ℕ}
    (f : BooleanCubeVertex m → ℂ) :
    booleanCubeCommutator f =
      (booleanCubeDirac m).comp (booleanCubeObservable f) -
        (booleanCubeObservable f).comp (booleanCubeDirac m) := by
  apply ContinuousLinearMap.ext
  intro ψ
  apply lp.ext
  funext e
  rw [ContinuousLinearMap.sub_apply, lp.coeFn_sub, Pi.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    booleanCubeDirac_apply, booleanCubeObservable_apply,
    booleanCubeObservable_apply, booleanCubeDirac_apply,
    booleanCubeCommutator_apply]
  rfl

/-- The global operator norm is bounded by the maximum local edge
gradient, by lp.mapCLM boundedness. -/
theorem booleanCubeCommutator_norm_le_cap {m : ℕ}
    (f : BooleanCubeVertex m → ℂ) :
    ‖booleanCubeCommutator f‖ ≤
      (booleanCubeGradientCap f : ℝ) := by
  exact lp.norm_mapCLM_le 2
    (booleanCubeLocalCommutator f)
    (NNReal.coe_nonneg (booleanCubeGradientCap f))
    (by
      intro e
      have h : ‖booleanCubeLocalCommutator f e‖₊ ≤
          booleanCubeGradientCap f := by
        unfold booleanCubeGradientCap
        exact Finset.le_sup (Finset.mem_univ e)
      exact_mod_cast h)

set_option maxHeartbeats 3000000 in
/-- The norm of a coordinatewise bounded map on arbitrary ℓ²
two-point blocks dominates the operator norm of each block. -/
theorem finiteIndexedHilbertBlock_norm_le_global
    {ι : Type*} [DecidableEq ι]
    (T : ι → EuclideanSpace ℂ (Fin 2) →L[ℂ]
      EuclideanSpace ℂ (Fin 2))
    (F : lp (fun _ : ι => EuclideanSpace ℂ (Fin 2)) 2 →L[ℂ]
      lp (fun _ : ι => EuclideanSpace ℂ (Fin 2)) 2)
    (hcoord : ∀ ψ : lp (fun _ : ι => EuclideanSpace ℂ (Fin 2)) 2,
      ∀ i : ι, (F ψ) i = T i (ψ i))
    (i : ι) :
    ‖T i‖ ≤ ‖F‖ := by
  let E : lp (fun _ : ι => EuclideanSpace ℂ (Fin 2)) 2 →L[ℂ]
      EuclideanSpace ℂ (Fin 2) :=
    lp.evalCLM ℂ (fun _ : ι => EuclideanSpace ℂ (Fin 2)) 2 i
  let S : EuclideanSpace ℂ (Fin 2) →L[ℂ]
      lp (fun _ : ι => EuclideanSpace ℂ (Fin 2)) 2 :=
    lp.singleContinuousLinearMap ℂ
      (fun _ : ι => EuclideanSpace ℂ (Fin 2)) 2 i
  have hcomp : T i = E.comp (F.comp S) := by
    apply ContinuousLinearMap.ext
    intro v
    change T i v = (F (lp.single 2 i v)) i
    rw [hcoord]
    simp
  have hE : ‖E‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound E (by norm_num)
    intro ψ
    change ‖ψ i‖ ≤ 1 * ‖ψ‖
    simpa only [one_mul] using
      (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) ψ i)
  have hS : ‖S‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound S (by norm_num)
    intro v
    calc
      ‖S v‖ = ‖lp.single 2 i v‖ := rfl
      _ = ‖v‖ := lp.norm_single
          (E := fun _ : ι => EuclideanSpace ℂ (Fin 2))
          (p := (2 : ENNReal)) (by norm_num) i v
      _ ≤ 1 * ‖v‖ := by simp
  have hInner : ‖F.comp S‖ ≤ ‖F‖ := by
    calc
      ‖F.comp S‖ ≤ ‖F‖ * ‖S‖ :=
        ContinuousLinearMap.opNorm_comp_le F S
      _ ≤ ‖F‖ * 1 :=
        mul_le_mul_of_nonneg_left hS (norm_nonneg F)
      _ = ‖F‖ := mul_one _
  calc
    ‖T i‖ = ‖E.comp (F.comp S)‖ := congrArg norm hcomp
    _ ≤ ‖E‖ * ‖F.comp S‖ :=
      ContinuousLinearMap.opNorm_comp_le E (F.comp S)
    _ ≤ 1 * ‖F.comp S‖ :=
      mul_le_mul_of_nonneg_right hE (norm_nonneg (F.comp S))
    _ = ‖F.comp S‖ := one_mul _
    _ ≤ ‖F‖ := hInner

/-- The commutator norm is at least the gradient on every edge. -/
theorem booleanCubeLocalGradient_le_global {m : ℕ}
    (f : BooleanCubeVertex m → ℂ) (e : BooleanCubeEdge m) :
    ‖f (booleanCubeEdgeUpper e) - f (booleanCubeEdgeLower e)‖ ≤
      ‖booleanCubeCommutator f‖ := by
  rw [← booleanCubeLocalCommutator_norm]
  classical
  exact finiteIndexedHilbertBlock_norm_le_global
    (booleanCubeLocalCommutator f)
    (booleanCubeCommutator f)
    (booleanCubeCommutator_apply f) e

/-- The global operator norm IS the finite supremum of all unit-edge
gradients, with the empty-edge maximum zero when m=0. -/
theorem booleanCubeCommutator_norm_eq_max {m : ℕ}
    (f : BooleanCubeVertex m → ℂ) :
    ‖booleanCubeCommutator f‖ =
      (booleanCubeGradientCap f : ℝ) := by
  apply le_antisymm
  · exact booleanCubeCommutator_norm_le_cap f
  · have h : booleanCubeGradientCap f ≤
        (⟨‖booleanCubeCommutator f‖, norm_nonneg _⟩ : NNReal) := by
      unfold booleanCubeGradientCap
      apply Finset.sup_le
      intro e _
      have he : ‖booleanCubeLocalCommutator f e‖ ≤
          ‖booleanCubeCommutator f‖ :=
        finiteIndexedHilbertBlock_norm_le_global
          (booleanCubeLocalCommutator f)
          (booleanCubeCommutator f)
          (booleanCubeCommutator_apply f) e
      exact_mod_cast he
    exact_mod_cast h

end

end Neoplatonic.LTR
