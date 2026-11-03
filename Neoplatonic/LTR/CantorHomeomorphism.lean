import Neoplatonic.LTR.NullaryCompleteness

/-!
# Homeomorphism of the one-axiom theory completion space with Cantor space

The bit decoder on actual mathlib complete types records membership of
the nullary predicate sentences. Each coordinate is continuous because
its truth locus is clopen. Compactness and Hausdorff separation then
turn the continuous bijection into a homeomorphism.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language
open Set

/-- Each truth coordinate defines a clopen subset of the Stone space. -/
theorem decode_coordinate_clopen (n : ℕ) :
    IsClopen {p : T.CompleteType Empty | decode p n = true} := by
  classical
  have h : {p : T.CompleteType Empty | decode p n = true} =
      T.typesWith (liftedAtom n) := by
    ext p
    simp [decode, FirstOrder.Language.Theory.typesWith]
  rw [h]
  exact FirstOrder.Language.Theory.CompleteType.isClopen_typesWith (T := T) (α := Empty)
    (liftedAtom n)

/-- The Boolean coordinate function is the indicator of its clopen locus. -/
theorem decode_coordinate_continuous (n : ℕ) :
    Continuous (fun p : T.CompleteType Empty => decode p n) := by
  classical
  let s : Set (T.CompleteType Empty) := T.typesWith (liftedAtom n)
  have hs : IsClopen s :=
    FirstOrder.Language.Theory.CompleteType.isClopen_typesWith (T := T)
      (α := Empty) (liftedAtom n)
  have heq : (fun p : T.CompleteType Empty => decode p n) =
      s.indicator (fun _ => true) := by
    funext p
    by_cases hp : p ∈ s
    · simp [decode, s, hp, Set.indicator_of_mem]
    · simp [decode, s, hp, Set.indicator_of_not_mem]
  rw [heq]
  exact hs.continuous_indicator continuous_const

/-- Coordinatewise continuity yields continuous decoding to the product. -/
theorem decode_continuous : Continuous decode := by
  apply continuous_pi
  intro n
  exact decode_coordinate_continuous n

/-- The previously proved two-sided inverses imply bijectivity. -/
theorem decode_bijective : Function.Bijective decode := by
  constructor
  · intro p q h
    have hp := congrArg encode h
    simpa [encode_decode] using hp
  · intro bits
    exact ⟨encode bits, decode_encode bits⟩

/-- Exact topological equivalence between Boolean streams and complete
first-order theories of the one-axiom nullary language. -/
noncomputable def cantorHomeomorph :
    (ℕ → Bool) ≃ₜ T.CompleteType Empty := by
  let e : T.CompleteType Empty ≃ (ℕ → Bool) :=
    Equiv.ofBijective decode decode_bijective
  exact (e.toHomeomorphOfContinuousClosed
    decode_continuous decode_continuous.isClosedMap).symm

end Neoplatonic.LTR.Nullary
