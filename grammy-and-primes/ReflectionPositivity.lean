import Neoplatonic.GodelGrounding
import Mathlib.Tactic

/-!
# Weighted reflection positivity and an ontological countermodel

Finite real spectra only. No theorem here identifies this finite form with
Weil's distribution, proves an analytic criterion for zeta, or proves RH.
The mathematical content is a negative witness for every moved reflection
orbit, followed by a model satisfying Scott, grounding, and A6 in which the
same witness remains negative. All substantive premises are arguments.
-/

noncomputable section
open scoped BigOperators
namespace GrammyAndPrimes.ReflectionPositivity

section Finite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A finite real analogue of a reflection-paired spectral form. -/
def reflectionForm (weight : ι → ℝ) (τ : ι → ι) (v : ι → ℝ) : ℝ :=
  ∑ i, weight i * v i * v (τ i)

/-- The antisymmetric vector supported on the orbit of a moved point. -/
def spike (τ : ι → ι) (a : ι) (i : ι) : ℝ :=
  if i = a then 1 else if i = τ a then -1 else 0

/-- Every moved two-cycle has an exact negative witness for positive weights.
Equal weights on paired indices are unnecessary for this real identity. -/
theorem negative_witness (weight : ι → ℝ) (τ : ι → ι)
    (hτ : Function.Involutive τ) (a : ι) (ha : τ a ≠ a) :
    reflectionForm weight τ (spike τ a) = -weight a - weight (τ a) := by
  have hterm (i : ι) :
      weight i * spike τ a i * spike τ a (τ i) =
        (if i = a then -weight a else 0) +
        (if i = τ a then -weight (τ a) else 0) := by
    by_cases hi : i = a
    · subst i
      simp [spike, ha, Ne.symm ha]
    · by_cases hj : i = τ a
      · subst i
        simp [spike, ha, hτ a]
      · simp [spike, hi, hj]
  unfold reflectionForm
  simp_rw [hterm]
  simp [Finset.sum_add_distrib, sub_eq_add_neg]

/-- Positivity on every vector forces the reflection to fix every index. -/
theorem positive_iff_fixed (weight : ι → ℝ) (τ : ι → ι)
    (hτ : Function.Involutive τ) (hweight : ∀ i, 0 < weight i) :
    (∀ v : ι → ℝ, 0 ≤ reflectionForm weight τ v) ↔
      (∀ i, τ i = i) := by
  constructor
  · intro h a
    by_contra ha
    have hn := h (spike τ a)
    rw [negative_witness weight τ hτ a ha] at hn
    have hwa := hweight a
    have hwb := hweight (τ a)
    linarith
  · intro h v
    unfold reflectionForm
    apply Finset.sum_nonneg
    intro i _
    rw [h i]
    simpa only [mul_assoc] using
      mul_nonneg (le_of_lt (hweight i)) (mul_self_nonneg (v i))

/-- The admissible tests must include a separating witness for each moved orbit. -/
theorem positive_on_separating_tests_forces_fixed
    (weight : ι → ℝ) (τ : ι → ι)
    (hτ : Function.Involutive τ) (hweight : ∀ i, 0 < weight i)
    (Test : (ι → ℝ) → Prop)
    (separates : ∀ a, τ a ≠ a → Test (spike τ a))
    (hpositive : ∀ v, Test v → 0 ≤ reflectionForm weight τ v) :
    ∀ i, τ i = i := by
  intro a
  by_contra ha
  have hn := hpositive (spike τ a) (separates a ha)
  rw [negative_witness weight τ hτ a ha] at hn
  have hwa := hweight a
  have hwb := hweight (τ a)
  linarith

/-- Reflection-invariant tests always look nonnegative, including on a bad orbit. -/
theorem invariant_test_nonnegative (weight : ι → ℝ) (τ : ι → ι)
    (hweight : ∀ i, 0 ≤ weight i) (v : ι → ℝ)
    (hv : ∀ i, v (τ i) = v i) : 0 ≤ reflectionForm weight τ v := by
  unfold reflectionForm
  apply Finset.sum_nonneg
  intro i _
  rw [hv i]
  simpa only [mul_assoc] using mul_nonneg (hweight i) (mul_self_nonneg (v i))

/-- Reflection covariance and positivity force coordinates onto the middle line. -/
theorem positive_forces_alignment (weight : ι → ℝ) (τ : ι → ι)
    (hτ : Function.Involutive τ) (hweight : ∀ i, 0 < weight i)
    (coord : ι → ℝ) (hcoord : ∀ i, coord (τ i) = 1 - coord i)
    (hpositive : ∀ v, 0 ≤ reflectionForm weight τ v) :
    ∀ i, coord i = (1 / 2 : ℝ) := by
  have hfixed := (positive_iff_fixed weight τ hτ hweight).mp hpositive
  intro i
  have hi := hcoord i
  rw [hfixed i] at hi
  linarith

/-- A proposed feature map must reproduce the specified reflection form.
The matching identity is an explicit assumption; mere existence of a norm
has no implication for this form. -/
theorem gram_realization_forces_fixed
    {κ : Type*} [Fintype κ]
    (weight : ι → ℝ) (τ : ι → ι)
    (hτ : Function.Involutive τ) (hweight : ∀ i, 0 < weight i)
    (A : (ι → ℝ) →ₗ[ℝ] (κ → ℝ))
    (matches : ∀ v, reflectionForm weight τ v = ∑ k, (A v k) ^ 2) :
    ∀ i, τ i = i := by
  apply (positive_iff_fixed weight τ hτ hweight).mp
  intro v
  rw [matches v]
  exact Finset.sum_nonneg (fun k _ => sq_nonneg (A v k))

/-- A zero weight can hide an entire orbit, hence the strict weight premise. -/
theorem zero_weights_nonnegative (τ : ι → ι) (v : ι → ℝ) :
    0 ≤ reflectionForm (fun _ => 0) τ v := by
  simp [reflectionForm]

end Finite

/-- Ordinary squared norms are nonnegative independently of any reflection. -/
theorem ordinary_norm_nonnegative {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    0 ≤ ∑ i, (v i) ^ 2 :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (v i))

theorem swap_involutive : Function.Involutive (fun b : Bool => !b) := by
  intro b
  cases b <;> rfl

/-- The two-point reflection gives -2 on its antisymmetric test. -/
theorem swap_negative :
    reflectionForm (fun (_ : Bool) => (1 : ℝ)) (fun b => !b)
      (spike (fun b => !b) false) = -2 := by
  have h := negative_witness (fun (_ : Bool) => (1 : ℝ))
    (fun b => !b) swap_involutive false (by decide)
  norm_num at h
  exact h

/-- Test restriction can conceal a negative mode completely. -/
theorem symmetric_tests_miss_negative_mode :
    (∀ v : Bool → ℝ, (∀ b, v (!b) = v b) →
      0 ≤ reflectionForm (fun _ => 1) (fun b => !b) v) ∧
    (∃ v : Bool → ℝ, reflectionForm (fun _ => 1) (fun b => !b) v < 0) := by
  constructor
  · intro v hv
    exact invariant_test_nonnegative (fun _ => 1) (fun b => !b)
      (fun _ => by norm_num) v hv
  · refine ⟨spike (fun b => !b) false, ?_⟩
    rw [swap_negative]
    norm_num

/-- An off-axis pair's unnormalized odd test becomes weak near the line. -/
theorem shrinking_odd_test (δ : ℝ) :
    δ * (-δ) + (-δ) * δ = -2 * δ ^ 2 := by
  ring

/-- Scott positivity concentrated at the actual root of the grounding model. -/
def rootScott : Neoplatonic.Godel.ScottTheory
    (fun (_ _ : Unit) => True) Bool where
  P := fun φ w => φ false w
  A1 := fun _ _ => Iff.rfl
  A2 := fun w _ _ h hb => hb w trivial false h
  A3 := fun _ _ h => h
  A4 := fun w _ h v _ => by cases w; cases v; exact h
  A5 := fun w _ hess v _ => ⟨false, by cases w; cases v; exact hess.1⟩

/-- Even identifying the Scott God-like being with the unique grounding root
through A6 leaves reflection positivity unentailed. This is a finite model,
with no alleged off-line zero of the actual zeta function. -/
theorem common_root_scott_a6_with_negative_reflection :
    ∃ (T : Neoplatonic.Godel.ScottTheory (fun (_ _ : Unit) => True) Bool)
      (G : Neoplatonic.GroundTheory Bool) (g : Bool),
      Neoplatonic.Godel.Godlike T.P g () ∧
      Neoplatonic.FirstPrinciple G.prior g ∧
      (∀ w : Unit, T.P (Neoplatonic.Godel.RootProp G.prior) w) ∧
      (∀ v : Bool → ℝ, 0 ≤ ∑ b, (v b) ^ 2) ∧
      (∃ v : Bool → ℝ,
        reflectionForm (fun _ => 1) (fun b => !b) v < 0) := by
  have hfp : Neoplatonic.FirstPrinciple
      Neoplatonic.Godel.twoBeingGround.prior false :=
    Neoplatonic.Godel.godlike_ne_firstPrinciple.2.2.1
  refine ⟨rootScott, Neoplatonic.Godel.twoBeingGround, false,
    ?_, hfp, ?_, ?_, symmetric_tests_miss_negative_mode.2⟩
  · intro φ hφ
    exact hφ
  · intro w
    exact hfp.1
  · exact ordinary_norm_nonnegative

#print axioms negative_witness
#print axioms positive_iff_fixed
#print axioms positive_on_separating_tests_forces_fixed
#print axioms invariant_test_nonnegative
#print axioms positive_forces_alignment
#print axioms gram_realization_forces_fixed
#print axioms zero_weights_nonnegative
#print axioms ordinary_norm_nonnegative
#print axioms swap_involutive
#print axioms swap_negative
#print axioms symmetric_tests_miss_negative_mode
#print axioms shrinking_odd_test
#print axioms common_root_scott_a6_with_negative_reflection

end GrammyAndPrimes.ReflectionPositivity
