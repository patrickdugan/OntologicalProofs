import Neoplatonic.LTR.ComplexObservableRepresentation
import Neoplatonic.LTR.ComplexDiracSelfAdjoint

/-!
# Bounded commutator on the infinite complex Dirac Hilbert space

For real observable values at two endpoints of each marked edge, with
uniform bounds |left_j|,|right_j| ≤ M and
|scale_j*(right_j-left_j)| ≤ L, the corresponding diagonal Hilbert
operator π(a) is bounded and preserves the maximal unbounded Dirac
domain. The unbounded commutator on that domain extends to the
bounded block-diagonal complex-linear map C, with ‖C‖≤L.

The proof uses the finite-block commutator identity and ℓ² closure.
It never treats the unbounded Dirac operator as a continuous map.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- Each actual two-point commutator block is a bounded complex map. -/
noncomputable def complexPairCommutatorBlock
    (mass scale left right : ℕ → ℝ) (j : ℕ) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  (complexEuclideanDiracBlock (mass j) (scale j)).comp
    (complexObservableBlock (left j) (right j)) -
  (complexObservableBlock (left j) (right j)).comp
    (complexEuclideanDiracBlock (mass j) (scale j))

/-- Exact norm of every marked-edge commutator block. -/
theorem complexPairCommutatorBlock_norm
    (mass scale left right : ℕ → ℝ) (j : ℕ) :
    ‖complexPairCommutatorBlock mass scale left right j‖ =
      |scale j * (right j - left j)| :=
  complexObservableBlock_commutator_norm
    (mass j) (scale j) (left j) (right j)

/-- Uniformly bounded commutator on the full infinite complex Hilbert sum. -/
noncomputable def complexPairCommutatorCLM
    (mass scale left right : ℕ → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hEdge : ∀ j, |scale j * (right j - left j)| ≤ L) :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
  lp.mapCLM 2 (complexPairCommutatorBlock mass scale left right)
    hL (fun j => by
      rw [complexPairCommutatorBlock_norm]
      exact hEdge j)

/-- Bounded commutator action at each marked edge. -/
theorem complexPairCommutatorCLM_apply
    (mass scale left right : ℕ → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hEdge : ∀ j, |scale j * (right j - left j)| ≤ L)
    (ψ : ComplexDiracBlockHilbert) (j : ℕ) :
    (complexPairCommutatorCLM mass scale left right L hL hEdge ψ) j =
      complexPairCommutatorBlock mass scale left right j (ψ j) := by
  change complexPairCommutatorBlock mass scale left right j (ψ j) = _
  rfl

/-- The infinite bounded commutator has norm at most the marked
Lipschitz quotient bound. -/
theorem complexPairCommutatorCLM_norm_le
    (mass scale left right : ℕ → ℝ) (L : ℝ)
    (hL : 0 ≤ L)
    (hEdge : ∀ j, |scale j * (right j - left j)| ≤ L) :
    ‖complexPairCommutatorCLM mass scale left right L hL hEdge‖ ≤ L :=
  lp.norm_mapCLM_le 2 (complexPairCommutatorBlock mass scale left right)
    hL (fun j => by
      rw [complexPairCommutatorBlock_norm]
      exact hEdge j)

/-- The finite-dimensional commutator is the exact failure of Dirac
action to commute with a diagonal two-point observable. -/
theorem complexDirac_observable_block_action
    (mass scale a b : ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    complexEuclideanDiracBlock mass scale (complexObservableBlock a b v) =
      complexObservableBlock a b (complexEuclideanDiracBlock mass scale v) +
        (((complexEuclideanDiracBlock mass scale).comp (complexObservableBlock a b)) -
         ((complexObservableBlock a b).comp (complexEuclideanDiracBlock mass scale))) v := by
  have h :
      complexEuclideanDiracBlock mass scale (complexObservableBlock a b v) -
        complexObservableBlock a b (complexEuclideanDiracBlock mass scale v) =
      (((complexEuclideanDiracBlock mass scale).comp (complexObservableBlock a b)) -
        ((complexObservableBlock a b).comp (complexEuclideanDiracBlock mass scale))) v := rfl
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

set_option maxHeartbeats 2000000 in
/-- A bounded observable satisfying the edge-quotient estimate maps
the maximal unbounded Dirac domain into itself. -/
theorem complexPairObservable_preserves_maximalDiracDomain
    (mass scale left right : ℕ → ℝ)
    (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hBound : ∀ j, |left j| ≤ M ∧ |right j| ≤ M)
    (hEdge : ∀ j, |scale j * (right j - left j)| ≤ L)
    (ψ : ComplexDiracBlockHilbert)
    (hψ : ψ ∈ maximalComplexDiracDomain mass scale) :
    complexPairObservableCLM left right M hM hBound ψ ∈
      maximalComplexDiracDomain mass scale := by
  let π := complexPairObservableCLM left right M hM hBound
  let C := complexPairCommutatorCLM mass scale left right L hL hEdge
  let D := maximalComplexDiracPMap mass scale
  change Memℓp (complexDiracBlockwise mass scale (π ψ)) 2
  have hcoords :
      complexDiracBlockwise mass scale (π ψ) =
        (((π (D ⟨ψ, hψ⟩)) + C ψ) :
          ℕ → EuclideanSpace ℂ (Fin 2)) := by
    funext j
    change complexEuclideanDiracBlock (mass j) (scale j) ((π ψ) j) =
      (π (D ⟨ψ, hψ⟩)) j + (C ψ) j
    rw [complexPairObservableCLM_apply, complexPairObservableCLM_apply,
      complexPairCommutatorCLM_apply]
    exact complexDirac_observable_block_action
      (mass j) (scale j) (left j) (right j) (ψ j)
  rw [hcoords]
  exact lp.memℓp _

/-- The domain commutator of the actual unbounded Dirac and the
bounded pairwise representation equals the bounded Hilbert map C. -/
theorem complexPairObservable_unbounded_commutator
    (mass scale left right : ℕ → ℝ)
    (M L : ℝ) (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hBound : ∀ j, |left j| ≤ M ∧ |right j| ≤ M)
    (hEdge : ∀ j, |scale j * (right j - left j)| ≤ L)
    (ψ : ComplexDiracBlockHilbert)
    (hψ : ψ ∈ maximalComplexDiracDomain mass scale) :
    (maximalComplexDiracPMap mass scale)
      ⟨complexPairObservableCLM left right M hM hBound ψ,
       complexPairObservable_preserves_maximalDiracDomain
         mass scale left right M L hM hL hBound hEdge ψ hψ⟩ -
    complexPairObservableCLM left right M hM hBound
      ((maximalComplexDiracPMap mass scale) ⟨ψ,hψ⟩) =
    complexPairCommutatorCLM mass scale left right L hL hEdge ψ := by
  apply lp.ext
  funext j
  simp only [lp.coeFn_sub, Pi.sub_apply]
  change complexEuclideanDiracBlock (mass j) (scale j)
      ((complexPairObservableCLM left right M hM hBound ψ) j) -
    (complexPairObservableCLM left right M hM hBound
      ((maximalComplexDiracPMap mass scale) ⟨ψ,hψ⟩)) j =
    (complexPairCommutatorCLM mass scale left right L hL hEdge ψ) j
  rw [complexPairObservableCLM_apply,
    complexPairObservableCLM_apply,
    complexPairCommutatorCLM_apply]
  change complexEuclideanDiracBlock (mass j) (scale j)
      (complexObservableBlock (left j) (right j) (ψ j)) -
    complexObservableBlock (left j) (right j)
      (complexEuclideanDiracBlock (mass j) (scale j) (ψ j)) =
    complexPairCommutatorBlock mass scale left right j (ψ j)
  rfl

end Neoplatonic.LTR
