import Neoplatonic.LTR.ComplexLipschitzAlgebra
import Neoplatonic.LTR.ComplexOrdinaryResolventCompact

/-!
# A constructed compact-resolvent complex spectral triple

The data are a dense complex star subalgebra of C(X, ℂ),
a faithful complex star-algebra representation on
H = ℓ²(ℕ, ℂ²), and a densely defined, closed, self-adjoint
partially defined complex-linear Dirac D. The bounded operator Q
is the two-sided ordinary resolvent (D - iI)⁻¹ and is compact.

For every f in the dense algebra, π(f) preserves Dom(D), and its
commutator Dπ(f) - π(f)D is the restriction of a bounded complex-linear
Hilbert operator. This is the standard compact-resolvent spectral
triple package, with the metric-recovery theorem available separately.

The marking assumptions appear in the explicit constructor.
Mass 2^j ensures compact resolvent regardless of the off-diagonal
inverse-distance couplings.
-/

namespace Neoplatonic.LTR

open scoped lp

/-- A concrete spectral-triple record for a compact metric space.
The ordinary resolvent fields specify its actual inverse equations,
rather than merely asserting compactness of an unrelated operator. -/
structure CompactComplexSpectralTriple
    (X : Type*) [MetricSpace X] [CompactSpace X] where
  observables : StarSubalgebra ℂ C(X, ℂ)
  representation : C(X, ℂ) →⋆ₐ[ℂ]
    (ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert)
  dirac : ComplexDiracBlockHilbert →ₗ.[ℂ] ComplexDiracBlockHilbert
  ordinaryResolvent :
    ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert
  observables_dense : observables.topologicalClosure = ⊤
  representation_faithful : Function.Injective representation
  dirac_dense : Dense (dirac.domain : Set ComplexDiracBlockHilbert)
  dirac_closed : dirac.IsClosed
  dirac_selfAdjoint : IsSelfAdjoint dirac
  resolvent_compact : IsCompactOperator ordinaryResolvent
  resolvent_domain :
    ∀ ψ : ComplexDiracBlockHilbert,
      ordinaryResolvent ψ ∈ dirac.domain
  resolvent_right :
    ∀ ψ : ComplexDiracBlockHilbert,
      dirac ⟨ordinaryResolvent ψ, resolvent_domain ψ⟩ -
        Complex.I • ordinaryResolvent ψ = ψ
  resolvent_left :
    ∀ (ψ : ComplexDiracBlockHilbert) (hψ : ψ ∈ dirac.domain),
      ordinaryResolvent (dirac ⟨ψ, hψ⟩ - Complex.I • ψ) = ψ
  bounded_commutator :
    ∀ (f : C(X, ℂ)), f ∈ observables →
      ∃ (L : ℝ)
        (C : ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert),
        0 ≤ L ∧ ‖C‖ ≤ L ∧
        ∀ (ψ : ComplexDiracBlockHilbert) (hψ : ψ ∈ dirac.domain),
          ∃ hπψ : representation f ψ ∈ dirac.domain,
            dirac ⟨representation f ψ, hπψ⟩ -
              representation f (dirac ⟨ψ, hψ⟩) = C ψ

/-- The canonical dense-Lipschitz spectral triple on a compact metric
space with a dense countable marked endpoint sequence. For its exact
metric recovery one additionally requires the marked edges to cover
all distinct ordered pairs in that dense sequence. -/
noncomputable def compactComplexMarkedSpectralTriple
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (left right : ℕ → X)
    (hdistinct : ∀ j, left j ≠ right j)
    (hEndpointCover : ∀ n, ∃ j, left j = q n ∨ right j = q n) :
    CompactComplexSpectralTriple X := by
  let scale : ℕ → ℝ := fun j => (dist (left j) (right j))⁻¹
  refine {
    observables := compactComplexLipschitzStarSubalgebra X
    representation := compactComplexObservableStarAlgHom left right
    dirac := maximalComplexDiracPMap (fun j => (2 : ℝ)^j) scale
    ordinaryResolvent := chosenComplexOrdinaryResolventCLM scale
    observables_dense := compactComplexLipschitz_dense X
    representation_faithful :=
      compactComplexObservableStarAlgHom_injective
        q hq left right hEndpointCover
    dirac_dense :=
      maximalComplexDiracDomain_dense (fun j => (2 : ℝ)^j) scale
    dirac_closed :=
      maximalComplexDiracPMap_isClosed (fun j => (2 : ℝ)^j) scale
    dirac_selfAdjoint :=
      maximalComplexDiracPMap_isSelfAdjoint (fun j => (2 : ℝ)^j) scale
    resolvent_compact := chosenComplexOrdinaryResolvent_isCompact scale
    resolvent_domain := ?_
    resolvent_right := ?_
    resolvent_left := ?_
    bounded_commutator := ?_
  }
  · intro ψ
    exact chosenComplexOrdinaryResolvent_mem_maximalComplexDiracDomain scale ψ
  · intro ψ
    exact chosenComplexOrdinaryResolvent_right_inverse scale ψ
  · intro ψ hψ
    exact chosenComplexOrdinaryResolvent_left_inverse scale ψ hψ
  · intro f hf
    obtain ⟨L, hL, hEdge⟩ :=
      compactComplexLipschitz_has_commutator_bound
        left right hdistinct f hf
    let C : ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert :=
      complexValuedPairCommutatorCLM
        (fun j => (2 : ℝ)^j) scale
        (fun j => f (left j)) (fun j => f (right j))
        L hL hEdge
    refine ⟨L, C, hL, ?_, ?_⟩
    · exact complexValuedPairCommutatorCLM_norm_le
        (fun j => (2 : ℝ)^j) scale
        (fun j => f (left j)) (fun j => f (right j))
        L hL hEdge
    · intro ψ hψ
      refine ⟨compactComplexStarAlgHom_preserves_maximalDiracDomain
        left right (fun j => (2 : ℝ)^j) scale
        f L hL hEdge ψ hψ, ?_⟩
      exact compactComplexStarAlgHom_unbounded_commutator
        left right (fun j => (2 : ℝ)^j) scale
        f L hL hEdge ψ hψ

/-- The constructed spectral triple recovers the original distance
whenever its edges cover all distinct ordered dense-sequence pairs.
The witness is itself in the dense Lipschitz star subalgebra. -/
theorem compactComplexMarkedSpectralTriple_metric_recovery
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (left right : ℕ → X)
    (hdistinct : ∀ j, left j ≠ right j)
    (hEndpointCover : ∀ n, ∃ j, left j = q n ∨ right j = q n)
    (hPairs : ∀ m n, q m ≠ q n →
      ∃ j : ℕ, left j = q m ∧ right j = q n)
    (x y : X) :
    (∀ (f : C(X, ℂ)),
       f ∈ (compactComplexMarkedSpectralTriple
         q hq left right hdistinct hEndpointCover).observables →
       ∀ (L : ℝ) (hL : 0 ≤ L)
         (hEdge : ∀ j,
           |(dist (left j) (right j))⁻¹| *
             ‖f (right j) - f (left j)‖ ≤ L),
       ‖complexValuedPairCommutatorCLM
         (fun j => (2 : ℝ)^j)
         (fun j => (dist (left j) (right j))⁻¹)
         (fun j => f (left j)) (fun j => f (right j))
         L hL hEdge‖ ≤ 1 →
       ‖f x - f y‖ ≤ dist x y) ∧
    ∃ (f : C(X, ℂ)),
      f ∈ (compactComplexMarkedSpectralTriple
        q hq left right hdistinct hEndpointCover).observables ∧
      ∃ (hEdge : ∀ j,
        |(dist (left j) (right j))⁻¹| *
          ‖f (right j) - f (left j)‖ ≤ 1),
        ‖complexValuedPairCommutatorCLM
          (fun j => (2 : ℝ)^j)
          (fun j => (dist (left j) (right j))⁻¹)
          (fun j => f (left j)) (fun j => f (right j))
          1 (by norm_num) hEdge‖ ≤ 1 ∧
        ‖f x - f y‖ = dist x y := by
  obtain ⟨hupper, ⟨f, hEdge, hnorm, heq⟩⟩ :=
    compactComplexStarAlgHom_metric_witness
      q hq left right hdistinct hPairs (fun j => (2 : ℝ)^j) x y
  constructor
  · intro a ha L hL hE hn
    exact hupper a L hL hE hn
  · refine ⟨f, ?_, hEdge, hnorm, heq⟩
    refine ⟨1, by norm_num, ?_⟩
    intro u v
    simpa only [one_mul] using
      ((denseMarkedComplexEdgeUnitBound_iff_lipschitz
        q hq left right hdistinct hPairs f f.continuous).mp hEdge) u v

end Neoplatonic.LTR
