import Neoplatonic.LTR.RealBounds

/-!
# Operator-observable version of the halting obstruction

The pullback norm on real unit-Lipschitz observables determines and is
determined by the map's metric Lipschitz bound. Consequently the property
that a computably given Cantor-space map has a uniformly bounded observable
pullback is undecidable.

Any separately constructed spectral realization with commutator seminorm
equal to Lip inherits this statement, but an operator-domain construction
is not taken as an axiom in this file.
-/

namespace Neoplatonic.LTR

universe u v

/-- An arbitrary real map bound is exactly the uniform bound on pullbacks
of all unit-Lipschitz observables. -/
theorem realMetricBound_iff_observableBound {X : Type u} {Y : Type v}
    (sx : X → ℕ → Bool) (sy : Y → ℕ → Bool) (f : X → Y) :
    (∃ C : ℝ, ∀ x y,
      markedDistance sy (f x) (f y) ≤ C * markedDistance sx x y) ↔
    (∃ C : ℝ, ∀ a : Y → ℝ,
      (∀ p q, |a p - a q| ≤ markedDistance sy p q) →
      ∀ x y, |a (f x) - a (f y)| ≤ C * markedDistance sx x y) := by
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro a ha x y
    exact (ha (f x) (f y)).trans (hC x y)
  · rintro ⟨C, h⟩
    refine ⟨C, ?_⟩
    intro x y
    have hv := h (fun z => markedDistance sy z (f y))
      (fun p q => markedDistance_observable_bound sy p q (f y)) x y
    simpa only [markedDistance_self, sub_zero,
      abs_of_nonneg (markedDistance_nonneg sy (f x) (f y))] using hv

/-- No algorithm decides whether all real unit-Lipschitz observables
remain uniformly Lipschitz after pullback by a computably presented
stream map generated from a partial-recursive program. -/
theorem finite_observable_pullback_undecidable :
    ¬ ComputablePred (fun e : Nat.Partrec.Code =>
      ∃ C : ℝ, ∀ a : (ℕ → Bool) → ℝ,
        (∀ p q, |a p - a q| ≤
          markedDistance (fun z : ℕ → Bool => z) p q) →
        ∀ x y, |a (acceleratedStream (stagedHalting e) x) -
                  a (acceleratedStream (stagedHalting e) y)| ≤
          C * markedDistance (fun z : ℕ → Bool => z) x y) := by
  intro hdec
  apply finite_real_lipschitz_undecidable
  apply ComputablePred.of_eq hdec
  intro e
  exact (realMetricBound_iff_observableBound
    (fun z : ℕ → Bool => z) (fun z : ℕ → Bool => z)
    (acceleratedStream (stagedHalting e))).symm

end Neoplatonic.LTR
