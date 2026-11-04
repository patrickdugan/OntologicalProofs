import Neoplatonic.LTR.ManifestationMarkedBlocks
import Mathlib.Data.Fintype.EquivFin

/-!
# Exact capacity for constrained logical profiles

The independent nullary language realizes all 2^m Boolean patterns,
but a general theory can impose dependencies between its m sentences.
The relevant capacity is the number of *realizable* profiles in the
image of the joint truth map, which may be far below 2^m.

Here X may be ANY type of models, consistent completions, control
states or other realizations, while B is a finite test-outcome space.
The profile map v : X → B need not be surjective.

The exact minimum number of sampled X-points needed to represent
every realized profile is the cardinality of Set.range v. The proof
constructs one canonical sample per realized profile and applies
finite-cardinality monotonicity to every covering sample.

This is a counting theorem about finite observation. Any semantic,
algorithmic or physical interpretation needs its own bridge.
-/

namespace Neoplatonic.LTR

universe u v

variable {X : Type u} {B : Type v} [Fintype B]

/-- The finite type of genuinely realizable observation profiles. -/
def RealizedProfiles (profile : X → B) : Type v :=
  {b : B // b ∈ Set.range profile}

/-- Exact abstract observational capacity of a possibly constrained
finite family of logical tests. Classical finite-range membership supplies
the finite enumeration, while the resulting cardinality is intrinsic. -/
noncomputable def realizedProfileCapacity (profile : X → B) : ℕ := by
  classical
  exact Fintype.card (RealizedProfiles profile)

/-- Every family that covers all realizable outcomes has at least
as many sample points as there are distinct realizable profiles. -/
theorem realizedProfileCapacity_lower_bound
    (profile : X → B) (n : ℕ) (samples : Fin n → X)
    (hcover : ∀ b : B, b ∈ Set.range profile →
      ∃ i : Fin n, profile (samples i) = b) :
    realizedProfileCapacity profile ≤ n := by
  classical
  classical
  have hsurj : Function.Surjective
      (fun i : Fin n =>
        (⟨profile (samples i), ⟨samples i, rfl⟩⟩ :
          RealizedProfiles profile)) := by
    intro b
    obtain ⟨i, hi⟩ := hcover b.val b.property
    refine ⟨i, ?_⟩
    apply Subtype.ext
    exact hi
  unfold realizedProfileCapacity
  simpa only [Fintype.card_fin] using
    (Fintype.card_le_of_surjective _ hsurj)

/-- One realization can be selected for every admissible profile.
No selection is required for impossible profiles. -/
theorem realizedProfileCapacity_attained
    (profile : X → B) :
    ∃ samples : Fin (realizedProfileCapacity profile) → X,
      ∀ b : B, b ∈ Set.range profile →
        ∃ i : Fin (realizedProfileCapacity profile),
          profile (samples i) = b := by
  classical
  letI : Fintype (RealizedProfiles profile) :=
    realizedProfilesFintype profile
  let e : Fin (realizedProfileCapacity profile) ≃
      RealizedProfiles profile := by
    unfold realizedProfileCapacity
    exact (Fintype.equivFin _).symm
  let samples : Fin (realizedProfileCapacity profile) → X :=
    fun i => Classical.choose (e i).property
  refine ⟨samples, ?_⟩
  intro b hb
  let b' : RealizedProfiles profile := ⟨b, hb⟩
  refine ⟨e.symm b', ?_⟩
  have hspec : profile (Classical.choose (e (e.symm b')).property) =
      (e (e.symm b')).val :=
    Classical.choose_spec (e (e.symm b')).property
  simpa only [samples, e.apply_symm_apply] using hspec

/-- Sharp constrained-profile capacity, independent of the number
of syntactic propositions used to define the finite observation. -/
theorem realizedProfileCapacity_exact
    (profile : X → B) :
    (∃ samples : Fin (realizedProfileCapacity profile) → X,
      ∀ b : B, b ∈ Set.range profile →
        ∃ i : Fin (realizedProfileCapacity profile),
          profile (samples i) = b) ∧
    (∀ (n : ℕ) (samples : Fin n → X),
      (∀ b : B, b ∈ Set.range profile →
        ∃ i : Fin n, profile (samples i) = b) →
      realizedProfileCapacity profile ≤ n) := by
  constructor
  · exact realizedProfileCapacity_attained profile
  · intro n samples h
    exact realizedProfileCapacity_lower_bound profile n samples h

end Neoplatonic.LTR
