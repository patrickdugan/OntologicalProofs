import Neoplatonic.LTR.NullaryCompleteness

/-!
# Cantor-space homeomorphism for the one-axiom nullary theory

Truth of the n-th predicate is a clopen coordinate in the space of
complete first-order theories. Therefore the coordinate decoder is
continuous. The companion classification proves it is bijective.
The domain is compact and the target is Hausdorff, so this bijection
is a homeomorphism by the standard compact-to-Hausdorff theorem.

The Boolean coordinates use the ordinary product topology (the same
topology as the first-disagreement PiNat metric).
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language
open Set

/-- The coordinate map into the Cantor stream is continuous. -/
theorem continuous_decode : Continuous decode := by
  apply continuous_pi_iff.mpr
  intro n
  have hc : IsClopen (T.typesWith (liftedAtom n)) :=
    Neoplatonic.LTR.locus_isClopen (T := T) (α := Empty) (liftedAtom n)
  have ht : {p : T.CompleteType Empty | decode p n = true} =
      T.typesWith (liftedAtom n) := by
    ext p
    simp [decode]
  have hf : {p : T.CompleteType Empty | decode p n = false} =
      (T.typesWith (liftedAtom n))ᶜ := by
    ext p
    simp [decode]
  have hb (b : Bool) :
      IsOpen {p : T.CompleteType Empty | decode p n = b} := by
    cases b with
    | false =>
        rw [hf]
        exact hc.1.isOpen_compl
    | true =>
        rw [ht]
        exact hc.2
  apply continuous_iff_isOpen.mpr
  intro s hs
  have heq : (fun p : T.CompleteType Empty => decode p n) ⁻¹' s =
      ⋃ b : s, {p : T.CompleteType Empty | decode p n = b.val} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro hp
      exact ⟨⟨decode p n, hp⟩, rfl⟩
    · rintro ⟨b, hb'⟩
      rw [hb']
      exact b.property
  rw [heq]
  exact isOpen_iUnion (fun b => hb b.val)

/-- The unique complete type with a specified Boolean truth assignment
is the one obtained from the corresponding singleton model. -/
theorem decode_bijective : Function.Bijective decode := by
  constructor
  · intro p q h
    have he := congrArg encode h
    simpa [encode_decode] using he
  · intro b
    exact ⟨encode b, decode_encode b⟩

/-- A homeomorphism between actual complete first-order theories of T
and Cantor space, using the natural product topology on Boolean streams. -/
noncomputable def cantorHomeomorph :
    T.CompleteType Empty ≃ₜ (ℕ → Bool) := by
  classical
  exact (Equiv.ofBijective decode decode_bijective).toHomeomorphOfContinuousClosed
    continuous_decode continuous_decode.isClosedMap

/-- The homeomorphism has the expected decoding action. -/
theorem cantorHomeomorph_apply (p : T.CompleteType Empty) :
    cantorHomeomorph p = decode p := rfl

/-- Its inverse returns the complete theory of the corresponding model. -/
theorem cantorHomeomorph_symm_apply (b : ℕ → Bool) :
    cantorHomeomorph.symm b = encode b := by
  apply decode_bijective.1
  simpa [cantorHomeomorph_apply] using (decode_encode b).symm

end Neoplatonic.LTR.Nullary
