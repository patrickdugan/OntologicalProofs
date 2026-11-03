import Neoplatonic.LTR.Filtered
import Neoplatonic.LTR.SpectralBridge

/-!
# Exact filtered reconstruction

For the dyadic metric, a delay of c is equivalent to a metric bound 2^c.
Testing the pullback on all real unit-Lipschitz observables is equivalent
to the same condition. These equivalences are quantified over actual
marked states; no completeness or existence of an arithmetic model is assumed.
The companion analytic construction identifies the observable seminorm
with an infinite Dirac commutator seminorm.
-/

namespace Neoplatonic.LTR

universe u v

/-- Prefixes are exactly the closed balls at dyadic scales. -/
theorem prefixAgreement_iff_distance_le {X : Type u}
    (mark : X → ℕ → Bool) (n : ℕ) (x y : X) :
    PrefixAgreement mark n x y ↔
      markedDistance mark x y ≤ (1 / 2 : ℝ)^n := by
  change (mark x ∈ PiNat.cylinder (mark y) n) ↔
    @dist (ℕ → Bool) PiNat.dist (mark x) (mark y) ≤ (1 / 2 : ℝ)^n
  exact PiNat.mem_cylinder_iff_dist_le

/-- Exact converse: a dyadic metric bound controls logical observation depth. -/
theorem translationDelay_iff_distance_bound {X : Type u} {Y : Type v}
    (sx : X → ℕ → Bool) (sy : Y → ℕ → Bool) (f : X → Y) (c : ℕ) :
    TranslationDelay sx sy f c ↔
      ∀ x y, markedDistance sy (f x) (f y) ≤
        (2 : ℝ)^c * markedDistance sx x y := by
  constructor
  · exact fun hf => markedDistance_le_of_delay hf
  · intro hf n x y h
    apply (prefixAgreement_iff_distance_le sy n (f x) (f y)).mpr
    have hs := (prefixAgreement_iff_distance_le sx (n + c) x y).mp h
    have hc : (2 : ℝ)^c * (1 / 2 : ℝ)^c = 1 := by
      rw [← mul_pow]
      norm_num
    calc
      markedDistance sy (f x) (f y) ≤
          (2 : ℝ)^c * markedDistance sx x y := hf x y
      _ ≤ (2 : ℝ)^c * (1 / 2 : ℝ)^(n + c) :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = (1 / 2 : ℝ)^n := by
        rw [pow_add]
        calc
          _ = ((2 : ℝ)^c * (1 / 2 : ℝ)^c) * (1 / 2 : ℝ)^n := by ring
          _ = _ := by rw [hc]; ring

/-- Distance to a fixed marked state is a unit-Lipschitz observable. -/
theorem markedDistance_observable_bound {X : Type u}
    (mark : X → ℕ → Bool) (x y z : X) :
    |markedDistance mark x z - markedDistance mark y z| ≤
      markedDistance mark x y := by
  have h1 : markedDistance mark x z ≤
      markedDistance mark x y + markedDistance mark y z :=
    PiNat.dist_triangle _ _ _
  have h2 : markedDistance mark y z ≤
      markedDistance mark y x + markedDistance mark x z :=
    PiNat.dist_triangle _ _ _
  rw [markedDistance_symm mark y x] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The complete quantitative reconstruction criterion. Once a faithful
Dirac realization satisfies L_D = Lip, its optimal pullback bound is
therefore the geometric and logical filtration bound simultaneously. -/
theorem translationDelay_iff_observable_bound {X : Type u} {Y : Type v}
    (sx : X → ℕ → Bool) (sy : Y → ℕ → Bool) (f : X → Y) (c : ℕ) :
    TranslationDelay sx sy f c ↔
      ∀ a : Y → ℝ,
        (∀ p q, |a p - a q| ≤ markedDistance sy p q) →
        ∀ x y, |a (f x) - a (f y)| ≤
          (2 : ℝ)^c * markedDistance sx x y := by
  rw [translationDelay_iff_distance_bound]
  constructor
  · intro hf a ha x y
    exact (ha _ _).trans (hf x y)
  · intro h x y
    have hv := h (fun z => markedDistance sy z (f y))
      (fun p q => markedDistance_observable_bound sy p q (f y)) x y
    simpa only [markedDistance_self, sub_zero,
      abs_of_nonneg (markedDistance_nonneg sy (f x) (f y))] using hv

end Neoplatonic.LTR
