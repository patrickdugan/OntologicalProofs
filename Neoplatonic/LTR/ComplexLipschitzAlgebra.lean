import Neoplatonic.LTR.ComplexCompactSpectralMetric
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-!
# Dense Lipschitz star subalgebra of continuous complex observables

On a compact metric space X, define the complex Lipschitz observables
as those f : C(X, ℂ) admitting some finite global real Lipschitz
constant. Closure under algebra operations and star is explicit.

The complex distance-to-point functions belong to this subalgebra
and separate distinct points. Complex Stone-Weierstrass therefore
proves density in C(X, ℂ).

Under inverse-distance marked couplings, every member also admits
a uniformly bounded infinite-Hilbert Dirac commutator.
-/

namespace Neoplatonic.LTR

/-- A continuous complex function has a finite global Lipschitz
constant. This is the admissible algebra for the marked Dirac. -/
def HasFiniteComplexLipschitzConstant
    {X : Type*} [MetricSpace X] (f : C(X, ℂ)) : Prop :=
  ∃ L : ℝ, 0 ≤ L ∧
    ∀ x y : X, ‖f x - f y‖ ≤ L * dist x y

/-- The finite-Lipschitz functions form a complex star subalgebra.
Compactness provides the uniform value bounds needed for products. -/
def compactComplexLipschitzStarSubalgebra
    (X : Type*) [MetricSpace X] [CompactSpace X] :
    StarSubalgebra ℂ C(X, ℂ) where
  carrier := {f | HasFiniteComplexLipschitzConstant f}
  zero_mem' := by
    refine ⟨0, le_refl _, ?_⟩
    intro x y
    simp
  one_mem' := by
    refine ⟨0, le_refl _, ?_⟩
    intro x y
    simp
  algebraMap_mem' c := by
    refine ⟨0, le_refl _, ?_⟩
    intro x y
    simp
  add_mem' := by
    intro f g
    rintro ⟨Lf, hLf, hf⟩ ⟨Lg, hLg, hg⟩
    refine ⟨Lf + Lg, add_nonneg hLf hLg, ?_⟩
    intro x y
    change ‖(f x + g x) - (f y + g y)‖ ≤ (Lf + Lg) * dist x y
    calc
      ‖(f x + g x) - (f y + g y)‖ =
          ‖(f x - f y) + (g x - g y)‖ := by congr 1; abel
      _ ≤ ‖f x - f y‖ + ‖g x - g y‖ := norm_add_le _ _
      _ ≤ Lf * dist x y + Lg * dist x y :=
        add_le_add (hf x y) (hg x y)
      _ = (Lf + Lg) * dist x y := by ring
  mul_mem' := by
    intro f g
    rintro ⟨Lf, hLf, hf⟩ ⟨Lg, hLg, hg⟩
    obtain ⟨Mf, hMf, hboundf⟩ :=
      compactContinuousComplex_has_bound f f.continuous
    obtain ⟨Mg, hMg, hboundg⟩ :=
      compactContinuousComplex_has_bound g g.continuous
    refine ⟨Lf * Mg + Mf * Lg,
      add_nonneg (mul_nonneg hLf hMg) (mul_nonneg hMf hLg), ?_⟩
    intro x y
    have hfirst :
        ‖f x - f y‖ * ‖g x‖ ≤ (Lf * dist x y) * Mg :=
      mul_le_mul (hf x y) (hboundg x)
        (norm_nonneg _) (mul_nonneg hLf dist_nonneg)
    have hsecond :
        ‖f y‖ * ‖g x - g y‖ ≤ Mf * (Lg * dist x y) :=
      mul_le_mul (hboundf y) (hg x y)
        (norm_nonneg _) hMf
    change ‖f x * g x - f y * g y‖ ≤
      (Lf * Mg + Mf * Lg) * dist x y
    calc
      ‖f x * g x - f y * g y‖ =
          ‖(f x - f y) * g x + f y * (g x - g y)‖ := by
            congr 1
            ring
      _ ≤ ‖(f x - f y) * g x‖ +
          ‖f y * (g x - g y)‖ := norm_add_le _ _
      _ = ‖f x - f y‖ * ‖g x‖ +
          ‖f y‖ * ‖g x - g y‖ := by rw [norm_mul, norm_mul]
      _ ≤ (Lf * dist x y) * Mg +
          Mf * (Lg * dist x y) := add_le_add hfirst hsecond
      _ = (Lf * Mg + Mf * Lg) * dist x y := by ring
  star_mem' := by
    intro f
    rintro ⟨L, hL, hf⟩
    refine ⟨L, hL, ?_⟩
    intro x y
    change ‖star (f x) - star (f y)‖ ≤ L * dist x y
    rw [← star_sub, norm_star]
    exact hf x y

/-- The complex-valued distance-to-target function is admissible. -/
theorem complexDistanceToPoint_mem_lipschitz
    {X : Type*} [MetricSpace X] [CompactSpace X] (y : X) :
    (⟨fun z : X => (dist z y : ℂ), by fun_prop⟩ : C(X, ℂ)) ∈
      compactComplexLipschitzStarSubalgebra X := by
  refine ⟨1, by norm_num, ?_⟩
  intro x z
  change ‖(dist x y : ℂ) - (dist z y : ℂ)‖ ≤
    (1 : ℝ) * dist x z
  simpa only [one_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] using abs_dist_sub_le x z y

/-- Distance-to-point observables separate points. -/
theorem compactComplexLipschitz_separatesPoints
    (X : Type*) [MetricSpace X] [CompactSpace X] :
    (compactComplexLipschitzStarSubalgebra X).SeparatesPoints := by
  intro x y hxy
  let f : C(X, ℂ) :=
    ⟨fun z => (dist z y : ℂ), by fun_prop⟩
  have hf : f ∈ compactComplexLipschitzStarSubalgebra X :=
    complexDistanceToPoint_mem_lipschitz y
  refine ⟨(f : X → ℂ), ⟨f, hf, rfl⟩, ?_⟩
  change (dist x y : ℂ) ≠ (dist y y : ℂ)
  simp only [dist_self, Complex.ofReal_zero]
  intro h
  have hz : dist x y = 0 := by exact_mod_cast h
  exact (ne_of_gt (dist_pos.mpr hxy)) hz

/-- Complex Stone-Weierstrass: finite-Lipschitz complex observables
are uniformly dense in the full continuous complex function algebra. -/
theorem compactComplexLipschitz_dense
    (X : Type*) [MetricSpace X] [CompactSpace X] :
    (compactComplexLipschitzStarSubalgebra X).topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (compactComplexLipschitzStarSubalgebra X)
    (compactComplexLipschitz_separatesPoints X)

/-- Every finite-Lipschitz observable has a bounded marked-edge
complex Dirac commutator under reciprocal-distance couplings. -/
theorem compactComplexLipschitz_has_commutator_bound
    {X : Type*} [MetricSpace X] [CompactSpace X]
    (left right : ℕ → X)
    (hdistinct : ∀ j, left j ≠ right j)
    (f : C(X, ℂ))
    (hf : f ∈ compactComplexLipschitzStarSubalgebra X) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ j,
      |(dist (left j) (right j))⁻¹| *
        ‖f (right j) - f (left j)‖ ≤ L := by
  obtain ⟨L, hL, hlip⟩ := hf
  refine ⟨L, hL, ?_⟩
  intro j
  exact (complexMarkedEdgeBound_iff
    (left j) (right j) (hdistinct j) f L).mpr
      (hlip (left j) (right j))

end Neoplatonic.LTR
