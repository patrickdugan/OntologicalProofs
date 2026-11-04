import Neoplatonic.LTR.BooleanCubeCapacity

/-!
# LTR-MAN-09D: Hamming geodesics from one-coordinate moves

The Hamming distance is exactly the number of coordinates on which
two Boolean truth assignments differ. If a complex observable changes
by norm at most one whenever precisely one coordinate changes, it
changes by at most Hamming distance between ANY two assignments.

The proof is a finite coordinate-repair argument. For x and y,
change one mismatching coordinate of x to y's bit. The Hamming
distance to y decreases by exactly one; the triangle inequality
and strong induction give the global Lipschitz bound.

This supplies the metric part of the hypercube Connes-distance proof
independently of the Dirac block calculations.
-/

namespace Neoplatonic.LTR

/-- Coordinate mismatch set for two Boolean assignments. -/
def booleanCubeMismatchSet {m : ℕ}
    (x y : BooleanCubeVertex m) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun i => x i ≠ y i)

/-- The mismatch-set cardinality is Mathlib's Hamming distance. -/
theorem booleanCubeMismatchSet_card {m : ℕ}
    (x y : BooleanCubeVertex m) :
    (booleanCubeMismatchSet x y).card = hammingDist x y := by
  rfl

/-- Changing one mismatching bit of x to y's value removes
exactly that mismatch from the mismatch set. -/
theorem booleanCubeMismatchSet_update {m : ℕ}
    (x y : BooleanCubeVertex m) (i : Fin m)
    (hi : x i ≠ y i) :
    booleanCubeMismatchSet (Function.update x i (y i)) y =
      (booleanCubeMismatchSet x y).erase i := by
  classical
  ext j
  by_cases hj : j = i
  · subst j
    simp [booleanCubeMismatchSet]
  · simp [booleanCubeMismatchSet, hj]

/-- One repair reduces the remaining Hamming distance by exactly one. -/
theorem booleanCube_hammingDist_update_match {m : ℕ}
    (x y : BooleanCubeVertex m) (i : Fin m)
    (hi : x i ≠ y i) :
    hammingDist (Function.update x i (y i)) y + 1 =
      hammingDist x y := by
  rw [← booleanCubeMismatchSet_card,
    ← booleanCubeMismatchSet_card,
    booleanCubeMismatchSet_update x y i hi]
  exact Finset.card_erase_add_one
    (by simp [booleanCubeMismatchSet, hi])

/-- Every repair of one mismatch makes a Hamming-one move. -/
theorem booleanCube_hammingDist_update_one {m : ℕ}
    (x y : BooleanCubeVertex m) (i : Fin m)
    (hi : x i ≠ y i) :
    hammingDist x (Function.update x i (y i)) = 1 := by
  classical
  have hf :
      (Finset.univ.filter
        (fun j : Fin m => x j ≠ Function.update x i (y i) j)) =
      ({i} : Finset (Fin m)) := by
    ext j
    by_cases hj : j = i
    · subst j
      simp [hi]
    · simp [hj]
  simpa [hammingDist, hf]

/-- A unit-edge gradient bound propagates along all Boolean
Hamming geodesics. This is the combinatorial core of the
Connes-distance upper bound. -/
theorem booleanCube_unitGradients_control_hamming
    {m : ℕ} (f : BooleanCubeVertex m → ℂ)
    (hedge : ∀ u v : BooleanCubeVertex m,
      hammingDist u v = 1 → ‖f u - f v‖ ≤ 1)
    (x y : BooleanCubeVertex m) :
    ‖f x - f y‖ ≤ (hammingDist x y : ℝ) := by
  have hmain : ∀ n : ℕ, ∀ x y : BooleanCubeVertex m,
      hammingDist x y = n →
        ‖f x - f y‖ ≤ (n : ℝ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u v hn
      by_cases hn0 : n = 0
      · have huv : u = v := hammingDist_eq_zero.mp (hn.trans hn0)
        subst v
        simp [hn0]
      · have huv : u ≠ v := by
          intro heq
          subst v
          simp at hn
          exact hn0 hn.symm
        have hdiff : ∃ i : Fin m, u i ≠ v i := by
          by_contra h
          push_neg at h
          exact huv (funext h)
        obtain ⟨i, hi⟩ := hdiff
        let w := Function.update u i (v i)
        have huw : hammingDist u w = 1 :=
          booleanCube_hammingDist_update_one u v i hi
        have hwv : hammingDist w v + 1 = n := by
          simpa only [w, hn] using
            (booleanCube_hammingDist_update_match u v i hi)
        have hlt : hammingDist w v < n := by omega
        have hrec : ‖f w - f v‖ ≤ (hammingDist w v : ℝ) :=
          ih (hammingDist w v) hlt w v rfl
        calc
          ‖f u - f v‖ = ‖(f u - f w) + (f w - f v)‖ := by
            congr 1
            abel
          _ ≤ ‖f u - f w‖ + ‖f w - f v‖ :=
            norm_add_le _ _
          _ ≤ 1 + (hammingDist w v : ℝ) :=
            add_le_add (hedge u w huw) hrec
          _ = (n : ℝ) := by
            exact_mod_cast (by omega :
              1 + hammingDist w v = n)
  exact hmain (hammingDist x y) x y rfl

end Neoplatonic.LTR
