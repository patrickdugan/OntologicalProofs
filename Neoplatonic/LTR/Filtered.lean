import Mathlib

/-!
# Filtered interpretations and quantitative reconstruction

A marking gives each state its sequence of Boolean observations. Agreement
through n observations defines the filtration. A translation of delay c
needs at most n+c source observations to determine n target observations.

The distance is mathlib's actual first-disagreement distance, pulled back
along the marking. It is a pseudometric in general; an injective marking
makes it a metric. No metric bound is assumed in the delay theorem.
-/

namespace Neoplatonic.LTR

universe u v w

/-- Equality of the first n Boolean observations. -/
def PrefixAgreement {X : Type u} (mark : X → ℕ → Bool)
    (n : ℕ) (x y : X) : Prop :=
  ∀ i, i < n → mark x i = mark y i

/-- A finite additive bound on the source depth needed for translation. -/
def TranslationDelay {X : Type u} {Y : Type v}
    (sx : X → ℕ → Bool) (sy : Y → ℕ → Bool)
    (f : X → Y) (c : ℕ) : Prop :=
  ∀ n x y, PrefixAgreement sx (n + c) x y →
    PrefixAgreement sy n (f x) (f y)

/-- Pull back the standard dyadic first-disagreement distance. -/
noncomputable def markedDistance {X : Type u}
    (mark : X → ℕ → Bool) (x y : X) : ℝ :=
  @dist (ℕ → Bool) PiNat.dist (mark x) (mark y)

theorem markedDistance_nonneg {X : Type u}
    (mark : X → ℕ → Bool) (x y : X) :
    0 ≤ markedDistance mark x y :=
  PiNat.dist_nonneg _ _

theorem markedDistance_self {X : Type u}
    (mark : X → ℕ → Bool) (x : X) :
    markedDistance mark x x = 0 :=
  PiNat.dist_self _

theorem markedDistance_symm {X : Type u}
    (mark : X → ℕ → Bool) (x y : X) :
    markedDistance mark x y = markedDistance mark y x :=
  PiNat.dist_comm _ _

theorem markedDistance_ultrametric {X : Type u}
    (mark : X → ℕ → Bool) (x y z : X) :
    markedDistance mark x z ≤
      max (markedDistance mark x y) (markedDistance mark y z) :=
  PiNat.dist_triangle_nonarch _ _ _

theorem markedDistance_separates {X : Type u}
    (mark : X → ℕ → Bool) (hinj : Function.Injective mark)
    (x y : X) (h : markedDistance mark x y = 0) : x = y := by
  apply hinj
  exact PiNat.eq_of_dist_eq_zero _ _ h

theorem prefixAgreement_mono {X : Type u}
    {mark : X → ℕ → Bool} {m n : ℕ} {x y : X}
    (h : PrefixAgreement mark n x y) (hmn : m ≤ n) :
    PrefixAgreement mark m x y := by
  intro i hi
  exact h i (lt_of_lt_of_le hi hmn)

theorem translationDelay_id {X : Type u} (mark : X → ℕ → Bool) :
    TranslationDelay mark mark id 0 := by
  intro n x y h
  simpa [PrefixAgreement] using h

/-- Delays add under composition, before any geometric realization. -/
theorem translationDelay_comp {X : Type u} {Y : Type v} {Z : Type w}
    {sx : X → ℕ → Bool} {sy : Y → ℕ → Bool} {sz : Z → ℕ → Bool}
    {f : X → Y} {g : Y → Z} {c d : ℕ}
    (hf : TranslationDelay sx sy f c) (hg : TranslationDelay sy sz g d) :
    TranslationDelay sx sz (g ∘ f) (c + d) := by
  intro n x y h
  apply hg n (f x) (f y)
  apply hf (n + d) x y
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Larger certified delays remain valid. -/
theorem translationDelay_mono {X : Type u} {Y : Type v}
    {sx : X → ℕ → Bool} {sy : Y → ℕ → Bool}
    {f : X → Y} {c d : ℕ} (hf : TranslationDelay sx sy f c)
    (hcd : c ≤ d) : TranslationDelay sx sy f d := by
  intro n x y h
  apply hf n x y
  exact prefixAgreement_mono h (Nat.add_le_add_left hcd n)

/-- First disagreement in the source is bounded by target disagreement plus delay. -/
theorem firstDifference_le_of_delay {X : Type u} {Y : Type v}
    {sx : X → ℕ → Bool} {sy : Y → ℕ → Bool}
    {f : X → Y} {c : ℕ} (hf : TranslationDelay sx sy f c)
    (x y : X) (hy : sy (f x) ≠ sy (f y)) :
    PiNat.firstDiff (sx x) (sx y) ≤
      PiNat.firstDiff (sy (f x)) (sy (f y)) + c := by
  by_contra hn
  have hprefix : PrefixAgreement sx
      (PiNat.firstDiff (sy (f x)) (sy (f y)) + 1 + c) x y := by
    intro i hi
    apply PiNat.apply_eq_of_lt_firstDiff
    omega
  have hout := hf (PiNat.firstDiff (sy (f x)) (sy (f y)) + 1) x y hprefix
  exact PiNat.apply_firstDiff_ne hy (hout _ (Nat.lt_succ_self _))

/-- Main quantitative theorem: c extra observations cost at most 2^c in distance. -/
theorem markedDistance_le_of_delay {X : Type u} {Y : Type v}
    {sx : X → ℕ → Bool} {sy : Y → ℕ → Bool}
    {f : X → Y} {c : ℕ} (hf : TranslationDelay sx sy f c)
    (x y : X) :
    markedDistance sy (f x) (f y) ≤
      (2 : ℝ)^c * markedDistance sx x y := by
  classical
  by_cases hy : sy (f x) = sy (f y)
  · have hz : markedDistance sy (f x) (f y) = 0 := by
      change @dist (ℕ → Bool) PiNat.dist (sy (f x)) (sy (f y)) = 0
      rw [hy]
      exact PiNat.dist_self _
    rw [hz]
    exact mul_nonneg (by positivity) (markedDistance_nonneg sx x y)
  · have hx : sx x ≠ sx y := by
      intro heq
      apply hy
      funext i
      exact hf (i + 1) x y (by intro k hk; exact congrFun heq k) i (by omega)
    have hk := firstDifference_le_of_delay hf x y hy
    have hp : (1 / 2 : ℝ)^(PiNat.firstDiff (sy (f x)) (sy (f y)) + c) ≤
        (1 / 2 : ℝ)^PiNat.firstDiff (sx x) (sx y) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
    have hc : (2 : ℝ)^c * (1 / 2 : ℝ)^c = 1 := by
      rw [← mul_pow]
      norm_num
    change @dist (ℕ → Bool) PiNat.dist (sy (f x)) (sy (f y)) ≤
      (2 : ℝ)^c * @dist (ℕ → Bool) PiNat.dist (sx x) (sx y)
    rw [PiNat.dist_eq_of_ne hy, PiNat.dist_eq_of_ne hx]
    calc
      (1 / 2 : ℝ)^PiNat.firstDiff (sy (f x)) (sy (f y)) =
          (2 : ℝ)^c * (1 / 2 : ℝ)^(PiNat.firstDiff (sy (f x)) (sy (f y)) + c) := by
        rw [pow_add]
        calc
          _ = (1 / 2 : ℝ)^PiNat.firstDiff (sy (f x)) (sy (f y)) *
              ((2 : ℝ)^c * (1 / 2 : ℝ)^c) := by rw [hc]; ring
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

/-- An inverse with bounded delay gives the reverse metric bound. -/
theorem markedDistance_reverse_of_inverse {X : Type u} {Y : Type v}
    {sx : X → ℕ → Bool} {sy : Y → ℕ → Bool}
    {f : X → Y} {g : Y → X} {d : ℕ}
    (hg : TranslationDelay sy sx g d) (hgf : Function.LeftInverse g f)
    (x y : X) :
    markedDistance sx x y ≤ (2 : ℝ)^d * markedDistance sy (f x) (f y) := by
  simpa [hgf x, hgf y] using markedDistance_le_of_delay hg (f x) (f y)

/-- Zero-delay equivalences preserve the marked metric exactly. -/
theorem zero_delay_isometry {X : Type u} {Y : Type v}
    {sx : X → ℕ → Bool} {sy : Y → ℕ → Bool}
    {f : X → Y} {g : Y → X}
    (hf : TranslationDelay sx sy f 0) (hg : TranslationDelay sy sx g 0)
    (hgf : Function.LeftInverse g f) (x y : X) :
    markedDistance sy (f x) (f y) = markedDistance sx x y := by
  apply le_antisymm
  · simpa using markedDistance_le_of_delay hf x y
  · simpa using markedDistance_reverse_of_inverse hg hgf x y

/-- Pullback of a Lipschitz observable obeys the same quantitative bound. -/
theorem observable_pullback_of_delay {X : Type u} {Y : Type v}
    {sx : X → ℕ → Bool} {sy : Y → ℕ → Bool}
    {f : X → Y} {c : ℕ} (hf : TranslationDelay sx sy f c)
    (a : Y → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (ha : ∀ y z, |a y - a z| ≤ K * markedDistance sy y z) :
    ∀ x y, |(a ∘ f) x - (a ∘ f) y| ≤
      (K * (2 : ℝ)^c) * markedDistance sx x y := by
  intro x y
  calc
    _ ≤ K * markedDistance sy (f x) (f y) := ha _ _
    _ ≤ K * ((2 : ℝ)^c * markedDistance sx x y) :=
      mul_le_mul_of_nonneg_left (markedDistance_le_of_delay hf x y) hK
    _ = _ := by ring

end Neoplatonic.LTR
