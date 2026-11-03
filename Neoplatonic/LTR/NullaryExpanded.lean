import Neoplatonic.LTR.NullaryClassification

/-!
# Classification in the language with no additional free constants

Actual complete types are complete theories in L[[Empty]]. The expanded
language has no genuinely new symbols because its constant index is Empty.
This is preparatory for the surjectivity of the singleton-model encoding.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.Structure

/-- An expanded-language model of the one-axiom theory is isomorphic
to the expanded singleton model with the same predicate values. -/
noncomputable def expandedModelIsoUnit (M : Type*)
    [L[[Empty]].Structure M] [Nonempty M]
    [M ⊨ (L.lhomWithConstants Empty).onTheory T] :
    @FirstOrder.Language.Equiv (L[[Empty]]) M Unit inferInstance
      (by
        letI : L.Structure M := (L.lhomWithConstants Empty).reduct M
        letI : L.Structure Unit := unitStructure (modelBits M)
        letI : (constantsOn Empty).Structure Unit :=
          constantsOn.structure (fun e : Empty => (e.elim : Unit))
        exact (inferInstance : L[[Empty]].Structure Unit)) := by
  classical
  letI : L.Structure M := (L.lhomWithConstants Empty).reduct M
  letI : M ⊨ T :=
    (LHom.onTheory_model (L.lhomWithConstants Empty) T).mp
      (inferInstance : M ⊨ (L.lhomWithConstants Empty).onTheory T)
  letI : Subsingleton M := subsingleton_of_model_T M
  letI : Inhabited M := Classical.inhabited_of_nonempty'
  letI : Unique M := Unique.mk' M
  letI : L.Structure Unit := unitStructure (modelBits M)
  letI : (constantsOn Empty).Structure Unit :=
    constantsOn.structure (fun e : Empty => (e.elim : Unit))
  letI : L[[Empty]].Structure Unit := inferInstance
  refine { Equiv.ofUnique M Unit with
    map_fun' := ?_
    map_rel' := ?_ }
  · intro n f xs
    cases f with
    | inl f => exact nomatch f
    | inr f =>
        cases n with
        | zero => exact nomatch f
        | succ n => exact nomatch f
  · intro n r xs
    cases r with
    | inl r =>
        cases n with
        | zero =>
            change ℕ at r
            change (modelBits M r = true) ↔
              @RelMap L M _ 0 (predSym r) xs
            rw [modelBits_iff M r]
            have hxs : (fun i : Fin 0 => (Fin.elim0 i : M)) = xs := by
              funext i
              exact Fin.elim0 i
            rw [hxs]
        | succ n => exact nomatch r
    | inr r => exact nomatch r

end Neoplatonic.LTR.Nullary
