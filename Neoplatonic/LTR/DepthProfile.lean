import Neoplatonic.LTR.Quantitative

/-!
# Least semantic observation depth

For any map of marked states with a finite source-prefix modulus at each
target depth, the least required source depth exists by Nat.find. This module
formalizes its sharp witness and the exact characterization of each integer
metric expansion threshold. No effective algorithm for computing the least
depth is implied by classical minimization.

The extended-real optimal Lipschitz constant
  Lip(f) = sup_{h_f(n)>0} 2^(h_f(n)-n)
is a separate analytic statement, discussed in FILTERED_SPECTRAL.md.
-/

namespace Neoplatonic.LTR

universe u v

/-- Knowing the first m source observations suffices to determine the first
n target observations. -/
def ObservedBy {X : Type u} {Y : Type v}
    (sx : X → ℕ → Bool) (sy : Y → ℕ → Bool)
    (f : X → Y) (n m : ℕ) : Prop :=
  ∀ x y, PrefixAgreement sx m x y → PrefixAgreement sy n (f x) (f y)

/-- Pointwise existence of some finite source depth. Continuity on compact
marked Stone spaces supplies this condition, but that theorem is separate. -/
def HasFiniteModulus {X : Type u} {Y : Type v}
    (sx : X → ℕ → Bool) (sy : Y → ℕ → Bool)
    (f : X → Y) : Prop :=
  ∀ n, ∃ m, ObservedBy sx sy f n m

/-- Classical least depth of an observation, without algorithmic claims. -/
noncomputable def leastDepth {X : Type u} {Y : Type v}
    (sx : X → ℕ → Bool) (sy : Y → ℕ → Bool)
    (f : X → Y) (h : HasFiniteModulus sx sy f) (n : ℕ) : ℕ := by
  classical
  exact Nat.find (h n)

/-- The chosen least depth determines the target prefix. -/
theorem leastDepth_sound {X : Type u} {Y : Type v}
    (sx : X → ℕ → Bool) (sy : Y → ℕ → Bool)
    (f : X → Y) (h : HasFiniteModulus sx sy f) (n : ℕ) :
    ObservedBy sx sy f n (leastDepth sx sy f h n) := by
  classical
  exact Nat.find_spec (h n)

/-- Any proposed observation depth is at least the least one. -/
theorem leastDepth_le {X : Type u} {Y : Type v}
    (sx : X → ℕ → Bool) (sy : Y → ℕ → Bool)
    (f : X → Y) (h : HasFiniteModulus sx sy f)
    (n m : ℕ) (hm : ObservedBy sx sy f n m) :
    leastDepth sx sy f h n ≤ m := by
  classical
  exact Nat.find_min' (h n) hm

/-- Zero target observations need zero source observations. -/
theorem leastDepth_zero {X : Type u} {Y : Type v}
    (sx : X → ℕ → Bool) (sy : Y → ℕ → Bool)
    (f : X → Y) (h : HasFiniteModulus sx sy f) :
    leastDepth sx sy f h 0 = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply leastDepth_le sx sy f h 0 0
  intro x y hp i hi
  omega

/-- Requesting more target observations cannot reduce the least source depth. -/
theorem leastDepth_mono {X : Type u} {Y : Type v}
    (sx : X → ℕ → Bool) (sy : Y → ℕ → Bool)
    (f : X → Y) (h : HasFiniteModulus sx sy f)
    {n m : ℕ} (hnm : n ≤ m) :
    leastDepth sx sy f h n ≤ leastDepth sx sy f h m := by
  apply leastDepth_le sx sy f h n (leastDepth sx sy f h m)
  intro x y hxy
  exact prefixAgreement_mono (leastDepth_sound sx sy f h m x y hxy) hnm

/-- A positive least depth is sharp: one fewer observation fails on
some pair of source states. This proof produces a genuine witness. -/
theorem leastDepth_sharp {X : Type u} {Y : Type v}
    (sx : X → ℕ → Bool) (sy : Y → ℕ → Bool)
    (f : X → Y) (h : HasFiniteModulus sx sy f)
    (n : ℕ) (hn : 0 < leastDepth sx sy f h n) :
    ∃ x y, PrefixAgreement sx (leastDepth sx sy f h n - 1) x y ∧
      ¬ PrefixAgreement sy n (f x) (f y) := by
  classical
  by_contra hno
  have hbetter : ObservedBy sx sy f n (leastDepth sx sy f h n - 1) := by
    intro x y hxy
    by_contra hout
    exact hno ⟨x, y, hxy, hout⟩
  have hm := leastDepth_le sx sy f h n (leastDepth sx sy f h n - 1) hbetter
  omega

/-- A uniform integer delay is exactly a uniform bound on the least depth. -/
theorem translationDelay_iff_leastDepth_le {X : Type u} {Y : Type v}
    (sx : X → ℕ → Bool) (sy : Y → ℕ → Bool)
    (f : X → Y) (h : HasFiniteModulus sx sy f) (c : ℕ) :
    TranslationDelay sx sy f c ↔
      ∀ n, leastDepth sx sy f h n ≤ n + c := by
  constructor
  · intro hf n
    exact leastDepth_le sx sy f h n (n + c) (hf n)
  · intro hf n x y hxy
    exact leastDepth_sound sx sy f h n x y
      (prefixAgreement_mono hxy (hf n))

/-- Thus an exact dyadic Lipschitz threshold can be read from the
least-depth profile, including cases with noninjective markings. -/
theorem leastDepth_bound_iff_metric_bound {X : Type u} {Y : Type v}
    (sx : X → ℕ → Bool) (sy : Y → ℕ → Bool)
    (f : X → Y) (h : HasFiniteModulus sx sy f) (c : ℕ) :
    (∀ n, leastDepth sx sy f h n ≤ n + c) ↔
      ∀ x y, markedDistance sy (f x) (f y) ≤
        (2 : ℝ)^c * markedDistance sx x y := by
  exact (translationDelay_iff_leastDepth_le sx sy f h c).symm.trans
    (translationDelay_iff_distance_bound sx sy f c)

/-- The same exact threshold is observable-theoretic. -/
theorem leastDepth_bound_iff_observable_bound {X : Type u} {Y : Type v}
    (sx : X → ℕ → Bool) (sy : Y → ℕ → Bool)
    (f : X → Y) (h : HasFiniteModulus sx sy f) (c : ℕ) :
    (∀ n, leastDepth sx sy f h n ≤ n + c) ↔
      ∀ a : Y → ℝ,
        (∀ p q, |a p - a q| ≤ markedDistance sy p q) →
        ∀ x y, |a (f x) - a (f y)| ≤
          (2 : ℝ)^c * markedDistance sx x y := by
  exact (translationDelay_iff_leastDepth_le sx sy f h c).symm.trans
    (translationDelay_iff_observable_bound sx sy f c)

/-- A finite global additive delay is precisely bounded additive excess
of the semantic least-depth profile. -/
theorem exists_delay_iff_bounded_depth_excess {X : Type u} {Y : Type v}
    (sx : X → ℕ → Bool) (sy : Y → ℕ → Bool)
    (f : X → Y) (h : HasFiniteModulus sx sy f) :
    (∃ c, TranslationDelay sx sy f c) ↔
      ∃ c, ∀ n, leastDepth sx sy f h n ≤ n + c := by
  simp only [translationDelay_iff_leastDepth_le sx sy f h]

end Neoplatonic.LTR
