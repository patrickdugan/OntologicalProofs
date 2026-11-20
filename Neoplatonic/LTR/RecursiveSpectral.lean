import Mathlib

/-!
# Recursive spectral certificates for looped reasoning

Finite-dimensional foundations for spectral mechanistic interpretability and
recursive self-improvement. These are unconditional matrix theorems; no claims
about an actual model's intelligence or about the Riemann hypothesis enter.

* Time-series Hankel matrices factor through their latent mode space.
* Intertwining transports all finite powers and preserves characteristic
  polynomials when the transport matrix has nonzero determinant.
* A two-state feedback cycle has an exact determinant and square identity.

The general analytic dynamical-zeta expansion, identification of neural
Koopman operators, and the physical meaning of an RSI eigenvalue remain
separate research questions.
-/

namespace Neoplatonic.LTR.RecursiveSpectral

/-- A finite mixture of exponential modes, arranged in Hankel form. -/
def hankel {m n r : ℕ} (lam amp : Fin r → ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  fun i j => ∑ k : Fin r, amp k * (lam k) ^ (i.val + j.val)

/-- Observations of each latent exponential mode. -/
def observation {m r : ℕ} (lam : Fin r → ℝ) :
    Matrix (Fin m) (Fin r) ℝ :=
  fun i k => (lam k) ^ i.val

/-- Reconstruction of the Hankel observations from each latent mode. -/
def reconstruction {n r : ℕ} (lam amp : Fin r → ℝ) :
    Matrix (Fin r) (Fin n) ℝ :=
  fun k j => amp k * (lam k) ^ j.val

/-- The Hankel matrix factors through a space of dimension r. -/
theorem hankel_factor {m n r : ℕ} (lam amp : Fin r → ℝ) :
    hankel (m := m) (n := n) lam amp =
      observation (m := m) lam * reconstruction (n := n) lam amp := by
  ext i j
  simp only [hankel, observation, reconstruction, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [pow_add]
  ring

/-- The rank of a finite Hankel matrix cannot exceed its number of modes. -/
theorem hankel_rank_le {m n r : ℕ} (lam amp : Fin r → ℝ) :
    (hankel (m := m) (n := n) lam amp).rank ≤ r := by
  rw [hankel_factor]
  calc
    (observation (m := m) lam * reconstruction (n := n) lam amp).rank
        ≤ (observation (m := m) lam).rank := Matrix.rank_mul_le_left _ _
    _ ≤ r := by
      simpa using (Matrix.rank_le_card_width (observation (m := m) lam))

/-- A representation transport that commutes with one update also commutes
with any number of repeated updates. -/
theorem intertwining_powers {n : ℕ}
    (A B L : Matrix (Fin n) (Fin n) ℝ)
    (h : B * L = L * A) (k : ℕ) :
    B ^ k * L = L * A ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      B ^ (k + 1) * L = B ^ k * (B * L) := by rw [pow_succ, mul_assoc]
      _ = B ^ k * (L * A) := by rw [h]
      _ = (B ^ k * L) * A := (mul_assoc _ _ _).symm
      _ = (L * A ^ k) * A := by rw [ih]
      _ = L * A ^ (k + 1) := by rw [pow_succ, mul_assoc]

/-- Invertible exact transport preserves all characteristic roots with
multiplicity. Nonzero determinant is an explicit hypothesis. -/
theorem intertwining_charpoly {n : ℕ}
    (A B L : Matrix (Fin n) (Fin n) ℝ)
    (hdet : L.det ≠ 0)
    (h : B * L = L * A) :
    B.charpoly = A.charpoly :=
  Matrix.charpoly_eq_of_mul_eq_mul hdet h

/-- The minimal weighted directed two-state feedback circuit. -/
def twoCycle (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![0, a; b, 0]

/-- Two passes through the circuit multiply each component by a*b. -/
theorem two_cycle_square (a b : ℝ) :
    twoCycle a b * twoCycle a b =
      (a * b) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [twoCycle, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- A concrete determinant denominator for the two-cycle zeta function. -/
theorem two_cycle_det (a b z : ℝ) :
    (!![1, -(z * a); -(z * b), 1] : Matrix (Fin 2) (Fin 2) ℝ).det =
      1 - a * b * z ^ 2 := by
  simp [Matrix.det_fin_two]
  ring

/-- An exact infinite geometric series for repeated traversals of one
primitive two-state cycle, valid within its convergence disk. -/
theorem two_cycle_zeta_series (a b z : ℝ)
    (h : |a * b * z ^ 2| < 1) :
    HasSum (fun k : ℕ => (a * b * z ^ 2) ^ k)
      ((!![1, -(z * a); -(z * b), 1] : Matrix (Fin 2) (Fin 2) ℝ).det)⁻¹ := by
  rw [two_cycle_det]
  exact hasSum_geometric_of_abs_lt_one h

#print axioms Neoplatonic.LTR.RecursiveSpectral.hankel_rank_le
#print axioms Neoplatonic.LTR.RecursiveSpectral.intertwining_charpoly
#print axioms Neoplatonic.LTR.RecursiveSpectral.two_cycle_det
#print axioms Neoplatonic.LTR.RecursiveSpectral.two_cycle_zeta_series

end Neoplatonic.LTR.RecursiveSpectral
