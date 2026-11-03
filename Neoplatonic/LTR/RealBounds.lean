import Neoplatonic.LTR.HaltingGeometry

/-!
# Arbitrary finite Lipschitz constants and effective undecidability

The existing dyadic theorem quantifies over bounds 2^c. Archimedean
unboundedness of powers of 2 makes this equivalent to existence of any
real-valued finite Lipschitz constant, with no positivity assumption on
the witness needed. The resulting geometric predicate is unconditionally
undecidable by mathlib's halting theorem.
-/

namespace Neoplatonic.LTR

universe u v

/-- Boundedness by an arbitrary real constant is equivalent to
boundedness by some integer power of two for the marked pseudometrics. -/
theorem realLipschitz_iff_dyadic {X : Type u} {Y : Type v}
    (sx : X → ℕ → Bool) (sy : Y → ℕ → Bool) (f : X → Y) :
    (∃ C : ℝ, ∀ x y, markedDistance sy (f x) (f y) ≤
      C * markedDistance sx x y) ↔
    (∃ c : ℕ, ∀ x y, markedDistance sy (f x) (f y) ≤
      (2 : ℝ)^c * markedDistance sx x y) := by
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨c, hc⟩ := pow_unbounded_of_one_lt C
      (show (1 : ℝ) < 2 by norm_num)
    refine ⟨c, ?_⟩
    intro x y
    exact (hC x y).trans
      (mul_le_mul_of_nonneg_right hc.le (markedDistance_nonneg sx x y))
  · rintro ⟨c, hc⟩
    exact ⟨(2 : ℝ)^c, hc⟩

/-- Fully geometric version: given a partial recursive program code,
there is no algorithm that decides whether its total Cantor-space map
has any finite real Lipschitz constant. -/
theorem finite_real_lipschitz_undecidable :
    ¬ ComputablePred (fun e : Nat.Partrec.Code =>
      ∃ C : ℝ, ∀ x y : ℕ → Bool,
        markedDistance (fun z : ℕ → Bool => z)
          (acceleratedStream (stagedHalting e) x)
          (acceleratedStream (stagedHalting e) y) ≤
          C * markedDistance (fun z : ℕ → Bool => z) x y) := by
  intro hreal
  apply dyadic_geometric_distortion_undecidable
  apply ComputablePred.of_eq hreal
  intro e
  exact realLipschitz_iff_dyadic
    (fun z : ℕ → Bool => z) (fun z : ℕ → Bool => z)
    (acceleratedStream (stagedHalting e))

end Neoplatonic.LTR
