import Neoplatonic.LTR.ComplexValuedDiracSeminorm
import Neoplatonic.LTR.ComplexDenseMarkedMetric

/-!
# Complex-valued marked commutator and dense metric reconstruction

The complex-valued Hilbert commutator has an exact operator norm equal
to the supremum of the edge gradients. For reciprocal-distance scales,
a norm-one commutator is equivalent to the unit Lipschitz condition
for continuous complex functions on a densely marked metric space.

The complex distance-to-target function gives an attaining witness.
The commutator is the bounded extension of the maximal-domain
unbounded Dirac commutator established in the preceding module.
-/

namespace Neoplatonic.LTR

/-- Continuous complex Lipschitz estimates extend from a dense pair
sequence to the full metric space. -/
theorem continuous_complex_lipschitz_of_dense_sequence
    {X : Type*} [MetricSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (a : X → ℂ) (ha : Continuous a) (L : ℝ)
    (hQ : ∀ m n, ‖a (q m) - a (q n)‖ ≤
      L * dist (q m) (q n)) :
    ∀ x y, ‖a x - a y‖ ≤ L * dist x y := by
  let S : Set (X × X) :=
    {p | ‖a p.1 - a p.2‖ ≤ L * dist p.1 p.2}
  have hleft : Continuous (fun p : X × X => ‖a p.1 - a p.2‖) :=
    ((ha.comp continuous_fst).sub (ha.comp continuous_snd)).norm
  have hright : Continuous (fun p : X × X => L * dist p.1 p.2) :=
    continuous_const.mul continuous_dist
  have hclosed : IsClosed S := by
    exact isClosed_le hleft hright
  have hdprod : DenseRange (Prod.map q q) := hq.prodMap hq
  have hsubset : Set.range (Prod.map q q) ⊆ S := by
    rintro p ⟨⟨m, n⟩, rfl⟩
    exact hQ m n
  have hall : Set.univ ⊆ S := by
    simpa only [hdprod.closure_eq] using
      (closure_minimal hsubset hclosed)
  intro x y
  exact hall (Set.mem_univ (x, y))

/-- The norm of a complex difference quotient is its endpoint
distance divided by the metric length of a nondegenerate edge. -/
theorem complexMarkedEdgeBound_iff
    {X : Type*} [MetricSpace X]
    (x y : X) (hxy : x ≠ y) (a : X → ℂ) (L : ℝ) :
    |(dist x y)⁻¹| * ‖a y - a x‖ ≤ L ↔
      ‖a x - a y‖ ≤ L * dist x y := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  rw [abs_of_nonneg (inv_nonneg.mpr hd.le), norm_sub_rev, mul_comm]
  exact (div_le_iff₀ hd)

/-- The unit ball of complex edge gradients on dense ordered marked
pairs is precisely the global complex 1-Lipschitz ball. -/
theorem denseMarkedComplexEdgeUnitBound_iff_lipschitz
    {X : Type*} [MetricSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (left right : ℕ → X)
    (hdistinct : ∀ j, left j ≠ right j)
    (hcover : ∀ m n, q m ≠ q n →
      ∃ j : ℕ, left j = q m ∧ right j = q n)
    (a : X → ℂ) (ha : Continuous a) :
    (∀ j, |(dist (left j) (right j))⁻¹| *
      ‖a (right j) - a (left j)‖ ≤ 1) ↔
    (∀ x y, ‖a x - a y‖ ≤ dist x y) := by
  constructor
  · intro hedge
    have hQ : ∀ m n, ‖a (q m) - a (q n)‖ ≤
        (1 : ℝ) * dist (q m) (q n) := by
      intro m n
      by_cases hmn : q m = q n
      · rw [hmn]
        simp
      · obtain ⟨j, hjl, hjr⟩ := hcover m n hmn
        have hj := (complexMarkedEdgeBound_iff
          (left j) (right j) (hdistinct j) a 1).mp (hedge j)
        simpa [hjl, hjr] using hj
    intro x y
    simpa only [one_mul] using
      continuous_complex_lipschitz_of_dense_sequence
        q hq a ha 1 hQ x y
  · intro hlip j
    apply (complexMarkedEdgeBound_iff
      (left j) (right j) (hdistinct j) a 1).mpr
    simpa only [one_mul] using hlip (left j) (right j)

/-- The norm-one ball of the actual bounded complex Hilbert Dirac
commutator equals the complex 1-Lipschitz ball. -/
theorem complexValuedDenseMarkedCommutator_norm_le_one_iff_lipschitz
    {X : Type*} [MetricSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (left right : ℕ → X)
    (hdistinct : ∀ j, left j ≠ right j)
    (hcover : ∀ m n, q m ≠ q n →
      ∃ j : ℕ, left j = q m ∧ right j = q n)
    (mass : ℕ → ℝ)
    (a : X → ℂ) (ha : Continuous a)
    (L : ℝ) (hL : 0 ≤ L)
    (hEdge : ∀ j,
      |(dist (left j) (right j))⁻¹| *
        ‖a (right j) - a (left j)‖ ≤ L) :
    ‖complexValuedPairCommutatorCLM
      mass
      (fun j => (dist (left j) (right j))⁻¹)
      (fun j => a (left j))
      (fun j => a (right j))
      L hL hEdge‖ ≤ 1 ↔
    ∀ x y : X, ‖a x - a y‖ ≤ dist x y := by
  exact (complexValuedPairCommutator_norm_le_iff
      mass
      (fun j => (dist (left j) (right j))⁻¹)
      (fun j => a (left j))
      (fun j => a (right j))
      L 1 hL hEdge (by norm_num)).trans
    (denseMarkedComplexEdgeUnitBound_iff_lipschitz
      q hq left right hdistinct hcover a ha)

/-- Complex continuous observables with a unit Dirac commutator
recover the exact metric; the distance-to-target function attains it. -/
theorem complexValuedDenseConnesDistance_operator_witness
    {X : Type*} [MetricSpace X]
    (q : ℕ → X) (hq : DenseRange q)
    (left right : ℕ → X)
    (hdistinct : ∀ j, left j ≠ right j)
    (hcover : ∀ m n, q m ≠ q n →
      ∃ j : ℕ, left j = q m ∧ right j = q n)
    (mass : ℕ → ℝ)
    (x y : X) :
    (∀ (a : X → ℂ), Continuous a →
       ∀ (L : ℝ) (hL : 0 ≤ L)
         (hEdge : ∀ j,
           |(dist (left j) (right j))⁻¹| *
             ‖a (right j) - a (left j)‖ ≤ L),
       ‖complexValuedPairCommutatorCLM
         mass
         (fun j => (dist (left j) (right j))⁻¹)
         (fun j => a (left j))
         (fun j => a (right j))
         L hL hEdge‖ ≤ 1 →
       ‖a x - a y‖ ≤ dist x y) ∧
    ∃ (a : X → ℂ) (ha : Continuous a)
      (hEdge : ∀ j,
        |(dist (left j) (right j))⁻¹| *
          ‖a (right j) - a (left j)‖ ≤ 1),
      ‖complexValuedPairCommutatorCLM
        mass
        (fun j => (dist (left j) (right j))⁻¹)
        (fun j => a (left j))
        (fun j => a (right j))
        1 (by norm_num) hEdge‖ ≤ 1 ∧
      ‖a x - a y‖ = dist x y := by
  constructor
  · intro a ha L hL hEdge hnorm
    exact ((complexValuedDenseMarkedCommutator_norm_le_one_iff_lipschitz
      q hq left right hdistinct hcover mass a ha L hL hEdge).mp hnorm) x y
  · have hcont : Continuous (fun z : X => (dist z y : ℂ)) := by fun_prop
    have hlip : ∀ p r : X,
        ‖(dist p y : ℂ) - (dist r y : ℂ)‖ ≤ dist p r := by
      intro p r
      simpa only [← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] using abs_dist_sub_le p r y
    have hEdge := (denseMarkedComplexEdgeUnitBound_iff_lipschitz
      q hq left right hdistinct hcover
      (fun z => (dist z y : ℂ)) hcont).mpr hlip
    refine ⟨fun z => (dist z y : ℂ), hcont, hEdge, ?_, ?_⟩
    · exact complexValuedPairCommutatorCLM_norm_le
        mass
        (fun j => (dist (left j) (right j))⁻¹)
        (fun j => (dist (left j) y : ℂ))
        (fun j => (dist (right j) y : ℂ))
        1 (by norm_num) hEdge
    · simp [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg dist_nonneg]

end Neoplatonic.LTR
