import Neoplatonic.LTR.ComplexValuedDenseMetric
import Neoplatonic.LTR.ComplexValuedStarAlgHom

/-!
# Compact complex observables on the maximal Dirac domain

For a compact space X the bundled faithful complex star-algebra
representation C(X, ℂ) → B(ℓ²(ℕ,ℂ²)) acts on the maximal domain
of the unbounded block Dirac when the represented observable has
a uniform marked-edge gradient bound. Its true unbounded commutator
is the bounded Hilbert operator from the complex-valued seminorm module.

On compact metric X with dense marked pairs and reciprocal-distance
couplings, the bounded commutator's unit norm ball recovers the metric.
The admissible observables have finite edge seminorm; this theorem
does not assert that every continuous function is Lipschitz.
-/

namespace Neoplatonic.LTR

/-- The bundled complex continuous-function representation preserves
the maximal unbounded Dirac domain under a finite edge-gradient bound. -/
theorem compactComplexStarAlgHom_preserves_maximalDiracDomain
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X)
    (mass scale : ℕ → ℝ)
    (f : C(X, ℂ)) (L : ℝ) (hL : 0 ≤ L)
    (hEdge : ∀ j,
      |scale j| * ‖f (right j) - f (left j)‖ ≤ L)
    (ψ : ComplexDiracBlockHilbert)
    (hψ : ψ ∈ maximalComplexDiracDomain mass scale) :
    (compactComplexObservableStarAlgHom left right f ψ) ∈
      maximalComplexDiracDomain mass scale := by
  exact complexValuedPairObservable_preserves_maximalDiracDomain
    mass scale (fun j => f (left j)) (fun j => f (right j))
    (compactComplexObservableBound f f.continuous) L
    (compactComplexObservableBound_nonneg f f.continuous) hL
    (fun j => ⟨compactComplexObservableBound_apply f f.continuous (left j),
      compactComplexObservableBound_apply f f.continuous (right j)⟩)
    hEdge ψ hψ

/-- For a complex continuous function with finite gradient bound,
the actual unbounded Dirac commutator with the bundled star-algebra
representation equals the bounded global Hilbert commutator. -/
theorem compactComplexStarAlgHom_unbounded_commutator
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (left right : ℕ → X)
    (mass scale : ℕ → ℝ)
    (f : C(X, ℂ)) (L : ℝ) (hL : 0 ≤ L)
    (hEdge : ∀ j,
      |scale j| * ‖f (right j) - f (left j)‖ ≤ L)
    (ψ : ComplexDiracBlockHilbert)
    (hψ : ψ ∈ maximalComplexDiracDomain mass scale) :
    (maximalComplexDiracPMap mass scale)
      ⟨compactComplexObservableStarAlgHom left right f ψ,
        compactComplexStarAlgHom_preserves_maximalDiracDomain
          left right mass scale f L hL hEdge ψ hψ⟩ -
      compactComplexObservableStarAlgHom left right f
        ((maximalComplexDiracPMap mass scale) ⟨ψ, hψ⟩) =
    complexValuedPairCommutatorCLM
      mass scale
      (fun j => f (left j)) (fun j => f (right j))
      L hL hEdge ψ := by
  exact complexValuedPairObservable_unbounded_commutator
    mass scale (fun j => f (left j)) (fun j => f (right j))
    (compactComplexObservableBound f f.continuous) L
    (compactComplexObservableBound_nonneg f f.continuous) hL
    (fun j => ⟨compactComplexObservableBound_apply f f.continuous (left j),
      compactComplexObservableBound_apply f f.continuous (right j)⟩)
    hEdge ψ hψ

/-- On compact metric X, complex continuous observables with bounded
Dirac commutator norm at most one recover the metric exactly. The
distance observable is a member of C(X,ℂ) and attains equality. -/
theorem compactComplexStarAlgHom_metric_witness
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (left right : ℕ → X)
    (hdistinct : ∀ j, left j ≠ right j)
    (hcover : ∀ m n, q m ≠ q n →
      ∃ j : ℕ, left j = q m ∧ right j = q n)
    (mass : ℕ → ℝ)
    (x y : X) :
    (∀ (f : C(X, ℂ)),
       ∀ (L : ℝ) (hL : 0 ≤ L)
         (hEdge : ∀ j,
           |(dist (left j) (right j))⁻¹| *
             ‖f (right j) - f (left j)‖ ≤ L),
       ‖complexValuedPairCommutatorCLM
         mass
         (fun j => (dist (left j) (right j))⁻¹)
         (fun j => f (left j)) (fun j => f (right j))
         L hL hEdge‖ ≤ 1 →
       ‖f x - f y‖ ≤ dist x y) ∧
    ∃ (f : C(X, ℂ))
      (hEdge : ∀ j,
        |(dist (left j) (right j))⁻¹| *
          ‖f (right j) - f (left j)‖ ≤ 1),
      ‖complexValuedPairCommutatorCLM
        mass
        (fun j => (dist (left j) (right j))⁻¹)
        (fun j => f (left j)) (fun j => f (right j))
        1 (by norm_num) hEdge‖ ≤ 1 ∧
      ‖f x - f y‖ = dist x y := by
  obtain ⟨hupper, ⟨a, ha, hEdge, hnorm, heq⟩⟩ :=
    complexValuedDenseConnesDistance_operator_witness
      q hq left right hdistinct hcover mass x y
  constructor
  · intro f L hL hE hnorm
    exact hupper f f.continuous L hL hE hnorm
  · exact ⟨⟨a, ha⟩, hEdge, hnorm, heq⟩

/-- The faithful complex star-algebra representation and metric
recovery theorem, bundled with explicit dense endpoint hypotheses. -/
theorem compactComplexStarAlgHom_faithful_metric_witness
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (left right : ℕ → X)
    (hEndpointCover : ∀ n, ∃ j, left j = q n ∨ right j = q n)
    (hdistinct : ∀ j, left j ≠ right j)
    (hcover : ∀ m n, q m ≠ q n →
      ∃ j : ℕ, left j = q m ∧ right j = q n)
    (mass : ℕ → ℝ) (x y : X) :
    Function.Injective (compactComplexObservableStarAlgHom left right) ∧
      ((∀ (f : C(X, ℂ)),
         ∀ (L : ℝ) (hL : 0 ≤ L)
           (hEdge : ∀ j,
             |(dist (left j) (right j))⁻¹| *
               ‖f (right j) - f (left j)‖ ≤ L),
         ‖complexValuedPairCommutatorCLM
           mass
           (fun j => (dist (left j) (right j))⁻¹)
           (fun j => f (left j)) (fun j => f (right j))
           L hL hEdge‖ ≤ 1 →
         ‖f x - f y‖ ≤ dist x y) ∧
      ∃ (f : C(X, ℂ))
        (hEdge : ∀ j,
          |(dist (left j) (right j))⁻¹| *
            ‖f (right j) - f (left j)‖ ≤ 1),
        ‖complexValuedPairCommutatorCLM
          mass
          (fun j => (dist (left j) (right j))⁻¹)
          (fun j => f (left j)) (fun j => f (right j))
          1 (by norm_num) hEdge‖ ≤ 1 ∧
        ‖f x - f y‖ = dist x y) := by
  constructor
  · exact compactComplexObservableStarAlgHom_injective
      q hq left right hEndpointCover
  · exact compactComplexStarAlgHom_metric_witness
      q hq left right hdistinct hcover mass x y

end Neoplatonic.LTR
