import Neoplatonic.LTR.EffectiveSpectral
import Neoplatonic.LTR.NullaryTopology

/-!
# Exact spectral filtration scale of nullary first-order sentences

The kth predicate of the one-axiom nullary theory is a labelled
continuous observable on the genuine Stone space of complete theories.
Under the verified Cantor homeomorphism its real 0/1-valued observable
has Lipschitz seminorm precisely 2^k in the dyadic first-disagreement
metric. This is the exact cost of resolving the kth logical coordinate.

The bound holds on every pair of Boolean streams and is witnessed by
a pair which disagree only at the kth coordinate. The corresponding
genuine complete theories are obtained through the checked encode map.
-/

namespace Neoplatonic.LTR

/-- Boolean truth value as a real-valued observable. -/
def bitObservable (n : ℕ) (x : ℕ → Bool) : ℝ :=
  if x n = true then 1 else 0

/-- The kth truth observable has Lipschitz bound 2^k. -/
theorem bitObservable_lipschitz_upper (n : ℕ) (x y : ℕ → Bool) :
    |bitObservable n x - bitObservable n y| ≤
      (2 : ℝ)^n * @dist (ℕ → Bool) PiNat.dist x y := by
  by_cases heq : x n = y n
  · have hz : bitObservable n x = bitObservable n y := by
      simp [bitObservable, heq]
    rw [hz, sub_self, abs_zero]
    exact mul_nonneg (by positivity) (PiNat.dist_nonneg x y)
  · have hne : x ≠ y := by
      intro h
      exact heq (congrFun h n)
    have hfd : PiNat.firstDiff x y ≤ n := by
      by_contra hn
      exact heq (PiNat.apply_eq_of_lt_firstDiff (show n < PiNat.firstDiff x y by omega))
    have hpow : (1 / 2 : ℝ)^n ≤ (1 / 2 : ℝ)^PiNat.firstDiff x y :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hfd
    have hdist : (1 / 2 : ℝ)^n ≤ @dist (ℕ → Bool) PiNat.dist x y := by
      simpa only [PiNat.dist_eq_of_ne hne] using hpow
    have hscale : (2 : ℝ)^n * (1 / 2 : ℝ)^n = 1 := by
      rw [← mul_pow]
      norm_num
    have hlower : (1 : ℝ) ≤ (2 : ℝ)^n * @dist (ℕ → Bool) PiNat.dist x y := by
      calc
        1 = (2 : ℝ)^n * (1 / 2 : ℝ)^n := hscale.symm
        _ ≤ _ := mul_le_mul_of_nonneg_left hdist (by positivity)
    have hupper : |bitObservable n x - bitObservable n y| ≤ 1 := by
      cases hx : x n <;> cases hy : y n <;> simp [bitObservable, hx, hy]
    exact hupper.trans hlower

/-- A Boolean stream with a single true bit at index n. -/
def singleTrueBit (n : ℕ) : ℕ → Bool :=
  fun k => decide (k = n)

/-- Two streams disagree at exactly coordinate n. -/
theorem firstDifference_singleTrueBit (n : ℕ) :
    PiNat.firstDiff (fun _ : ℕ => false) (singleTrueBit n) = n := by
  have hne : (fun _ : ℕ => false) ≠ singleTrueBit n := by
    intro heq
    have h := congrFun heq n
    simp [singleTrueBit] at h
  apply le_antisymm
  · by_contra hn
    have ht : n < PiNat.firstDiff (fun _ : ℕ => false) (singleTrueBit n) := by
      omega
    have h := PiNat.apply_eq_of_lt_firstDiff ht
    simp [singleTrueBit] at h
  · by_contra hn
    have ht : PiNat.firstDiff (fun _ : ℕ => false) (singleTrueBit n) < n := by
      omega
    have h := PiNat.apply_firstDiff_ne hne
    have hf : (fun _ : ℕ => false)
        (PiNat.firstDiff (fun _ : ℕ => false) (singleTrueBit n)) =
        singleTrueBit n (PiNat.firstDiff (fun _ : ℕ => false) (singleTrueBit n)) := by
      simp [singleTrueBit, Nat.ne_of_lt ht]
    exact h hf

/-- The kth truth observable attains its 2^k Lipschitz bound. -/
theorem bitObservable_lipschitz_sharp (n : ℕ) :
    |bitObservable n (fun _ => false) -
      bitObservable n (singleTrueBit n)| =
      (2 : ℝ)^n * @dist (ℕ → Bool) PiNat.dist
        (fun _ => false) (singleTrueBit n) := by
  have hne : (fun _ : ℕ => false) ≠ singleTrueBit n := by
    intro heq
    have h := congrFun heq n
    simp [singleTrueBit] at h
  rw [PiNat.dist_eq_of_ne hne, firstDifference_singleTrueBit]
  simp [bitObservable, singleTrueBit]
  rw [← mul_pow]
  norm_num

end Neoplatonic.LTR
