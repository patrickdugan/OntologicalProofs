import Neoplatonic.LTR.NullaryCompleteness
import Neoplatonic.LTR.NullarySemantics
import Neoplatonic.LTR.RealBounds

/-!
# Undecidable metric regularity on actual first-order completion spaces

The Cantor stream family F_e has a corresponding action on the complete
theories of a single finitely axiomatized first-order theory. The action
is the syntax-induced translation represented in NullaryHalting and
NullarySemantics, with the code of e as its finite input.

The decoder supplies a canonical dyadic distance on complete types. The
previous halting-hardness theorem transfers exactly along the checked
two-sided inverse of encode and decode. This is a theorem about the
metric geometry of *genuine first-order complete theories*.

No claims of intrinsic choice-free geometry, theological consequence,
or a novel form of arithmetic incompleteness are implied.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language

/-- The action of a program on the space of actual complete first-order
theories, conjugated through the Boolean valuation correspondence. -/
noncomputable def typeAction (e : Nat.Partrec.Code)
    (p : T.CompleteType Empty) : T.CompleteType Empty :=
  encode (acceleratedStream (stagedHalting e) (decode p))

/-- The type action has the intended Boolean coordinates. -/
theorem decode_typeAction (e : Nat.Partrec.Code) (p : T.CompleteType Empty) :
    decode (typeAction e p) =
      acceleratedStream (stagedHalting e) (decode p) := by
  exact decode_encode _

/-- The transformed n-th atomic truth value is the original atom at the
reindexed source coordinate, making the action explicitly syntactic. -/
theorem liftedAtom_mem_typeAction (e : Nat.Partrec.Code)
    (p : T.CompleteType Empty) (n : ℕ) :
    liftedAtom n ∈ typeAction e p ↔
      liftedAtom (haltingIndex e n) ∈ p := by
  rw [typeAction, liftedAtom_mem_encode]
  rw [← haltingIndex_stream e (decode p) n]
  classical
  simp [decode]

/-- Pull back the dyadic first-disagreement distance along the complete
type/valuation equivalence. It is a genuine metric since decode is bijective. -/
noncomputable def completeTypeDyadicDistance
    (p q : T.CompleteType Empty) : ℝ :=
  markedDistance decode p q

/-- A uniform real Lipschitz bound on transformed complete theories is
equivalent to the same bound for the original Cantor-stream map. -/
theorem typeAction_lipschitz_iff (e : Nat.Partrec.Code) :
    (∃ C : ℝ, ∀ p q : T.CompleteType Empty,
       completeTypeDyadicDistance (typeAction e p) (typeAction e q) ≤
         C * completeTypeDyadicDistance p q) ↔
    (∃ C : ℝ, ∀ x y : ℕ → Bool,
       markedDistance (fun z : ℕ → Bool => z)
         (acceleratedStream (stagedHalting e) x)
         (acceleratedStream (stagedHalting e) y) ≤
       C * markedDistance (fun z : ℕ → Bool => z) x y) := by
  constructor
  · rintro ⟨C, h⟩
    refine ⟨C, ?_⟩
    intro x y
    have hxy := h (encode x) (encode y)
    simpa only [completeTypeDyadicDistance, typeAction, decode_encode] using hxy
  · rintro ⟨C, h⟩
    refine ⟨C, ?_⟩
    intro p q
    have hxy := h (decode p) (decode q)
    simpa only [completeTypeDyadicDistance, typeAction, decode_encode] using hxy

/-- A Gödelian computability obstruction formulated entirely on the genuine
complete-type space of a finitely axiomatized first-order theory. -/
theorem completeType_geometry_undecidable :
    ¬ ComputablePred (fun e : Nat.Partrec.Code =>
      ∃ C : ℝ, ∀ p q : T.CompleteType Empty,
        completeTypeDyadicDistance (typeAction e p) (typeAction e q) ≤
          C * completeTypeDyadicDistance p q) := by
  intro h
  apply finite_real_lipschitz_undecidable
  apply ComputablePred.of_eq h
  intro e
  exact (typeAction_lipschitz_iff e).symm

end Neoplatonic.LTR.Nullary
