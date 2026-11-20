import Mathlib

/-!
# Walsh--Fourier energy certificates on every finite Boolean cube

`Cube n` is the set of n-bit strings, represented recursively.  `character` is
the usual parity character, and `walsh` is the normalized Walsh--Hadamard
transform.  Its finite character-sum formula fixes the normalization explicitly.

Parseval and the residual-energy identity hold for every real-valued function
on every finite cube.  Applying them to model activations requires a separately
specified Boolean intervention map and the uniform measure used here.
-/

namespace Neoplatonic.LTR.WalshFourier

open scoped BigOperators

/-- A recursively represented n-bit Boolean cube. -/
def Cube : ℕ → Type
  | 0 => Unit
  | n + 1 => Bool × Cube n

instance cubeFintype (n : ℕ) : Fintype (Cube n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Bool × Cube n))

theorem card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  induction n with
  | zero =>
    letI : Unique (Cube 0) := { default := (), uniq := fun x => by cases x; rfl }
    simp only [Fintype.card_unique, pow_zero]
  | succ n ih =>
    change Fintype.card (Bool × Cube n) = 2 ^ (n + 1)
    simp [Fintype.card_prod, ih, pow_succ, Nat.mul_comm]

/-- The parity character, with one minus sign for each jointly true bit. -/
def character : (n : ℕ) → Cube n → Cube n → ℝ
  | 0, _, _ => 1
  | n + 1, s, x =>
      (if s.1 then (if x.1 then -1 else 1) else 1) *
        character n s.2 x.2

/-- The normalized Walsh--Hadamard recursion. -/
noncomputable def walsh : (n : ℕ) → (Cube n → ℝ) → Cube n → ℝ
  | 0, f, _ => f ()
  | n + 1, f, s =>
      if s.1 then
        walsh n (fun x => f (false, x) - f (true, x)) s.2 / 2
      else
        walsh n (fun x => f (false, x) + f (true, x)) s.2 / 2

/-- The recursion computes the standard uniformly normalized character sum. -/
theorem walsh_eq_character_sum (n : ℕ) (f : Cube n → ℝ) (s : Cube n) :
    walsh n f s = (∑ x : Cube n, f x * character n s x) / (2 : ℝ) ^ n := by
  induction n with
  | zero =>
    letI : Unique (Cube 0) := { default := (), uniq := fun x => by cases x; rfl }
    simp only [walsh, character, mul_one, pow_zero, div_one, Fintype.sum_unique]
    exact congrArg f (Subsingleton.elim () default)
  | succ n ih =>
    obtain ⟨b, s⟩ := s
    change walsh (n + 1) f (b, s) =
      (∑ x : Bool × Cube n, f x * character (n + 1) (b, s) x) / (2 : ℝ) ^ (n + 1)
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    cases b <;>
      simp [walsh, character, ih,
        add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_neg_distrib, pow_succ] <;> ring

/-- Parseval's identity for all real functions on all finite Boolean cubes. -/
theorem parseval (n : ℕ) (f : Cube n → ℝ) :
    (∑ s : Cube n, (walsh n f s) ^ 2) =
      (∑ x : Cube n, (f x) ^ 2) / (2 : ℝ) ^ n := by
  induction n with
  | zero =>
    letI : Unique (Cube 0) := { default := (), uniq := fun x => by cases x; rfl }
    simp only [walsh, pow_zero, div_one, Fintype.sum_unique]
    exact congrArg (fun x : Cube 0 => (f x) ^ 2) (Subsingleton.elim () default)
  | succ n ih =>
    have hsum :
        (∑ x : Cube n, (f (false, x) - f (true, x)) ^ 2) +
            (∑ x : Cube n, (f (false, x) + f (true, x)) ^ 2) =
          2 * (∑ x : Cube n, ((f (false, x)) ^ 2 + (f (true, x)) ^ 2)) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    calc
      (∑ s : Cube (n + 1), (walsh (n + 1) f s) ^ 2) =
          ((∑ x : Cube n, (f (false, x) - f (true, x)) ^ 2) +
            (∑ x : Cube n, (f (false, x) + f (true, x)) ^ 2)) /
            (4 * (2 : ℝ) ^ n) := by
        change (∑ s : Bool × Cube n, (walsh (n + 1) f s) ^ 2) = _
        rw [Fintype.sum_prod_type, Fintype.sum_bool]
        change
          (∑ s : Cube n,
            (walsh n (fun x => f (false, x) - f (true, x)) s / 2) ^ 2) +
          (∑ s : Cube n,
            (walsh n (fun x => f (false, x) + f (true, x)) s / 2) ^ 2) = _
        simp_rw [div_pow]
        rw [← Finset.sum_div, ← Finset.sum_div, ih, ih]
        ring
      _ = (2 * (∑ x : Cube n, ((f (false, x)) ^ 2 + (f (true, x)) ^ 2))) /
          (4 * (2 : ℝ) ^ n) := by rw [hsum]
      _ = (∑ x : Cube (n + 1), (f x) ^ 2) / (2 : ℝ) ^ (n + 1) := by
        change _ = (∑ x : Bool × Cube n, (f x) ^ 2) / (2 : ℝ) ^ (n + 1)
        rw [Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib,
          pow_succ]
        ring

theorem walsh_sub (n : ℕ) (f g : Cube n → ℝ) (s : Cube n) :
    walsh n (fun x => f x - g x) s = walsh n f s - walsh n g s := by
  rw [walsh_eq_character_sum, walsh_eq_character_sum, walsh_eq_character_sum]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  ring

/-- Uniform mean squared error equals the exact squared coefficient error. -/
theorem residual_energy (n : ℕ) (f g : Cube n → ℝ) :
    (∑ x : Cube n, (f x - g x) ^ 2) / (2 : ℝ) ^ n =
      ∑ s : Cube n, (walsh n f s - walsh n g s) ^ 2 := by
  rw [← parseval n (fun x => f x - g x)]
  simp_rw [walsh_sub]

/-- Any one Fourier coefficient gives a lower bound on total mean squared error. -/
theorem coefficient_error_le (n : ℕ) (f g : Cube n → ℝ) (s : Cube n) :
    (walsh n f s - walsh n g s) ^ 2 ≤
      (∑ x : Cube n, (f x - g x) ^ 2) / (2 : ℝ) ^ n := by
  rw [residual_energy]
  exact Finset.single_le_sum
    (f := fun t : Cube n => (walsh n f t - walsh n g t) ^ 2)
    (fun t _ => sq_nonneg (walsh n f t - walsh n g t)) (Finset.mem_univ s)


end Neoplatonic.LTR.WalshFourier
