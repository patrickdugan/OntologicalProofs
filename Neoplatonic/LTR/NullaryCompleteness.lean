import Neoplatonic.LTR.NullaryExpanded
import Neoplatonic.LTR.NullaryTypes

/-!
# Every complete theory of the nullary singleton-domain language is a
# Boolean truth assignment

We realize an arbitrary complete type in a genuine model of its maximal
consistent theory. The unique-element axiom makes that model a singleton.
The empty-constant language isomorphism identifies its entire first-order
theory with the explicit singleton model determined by its relation bits.

No quantifier-elimination assumption or new axiom is introduced.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language

/-- The expanded-language structure used to realize a Boolean stream. -/
@[instance_reducible]
def expandedUnitStructure (bits : ℕ → Bool) : L[[Empty]].Structure Unit := by
  letI : L.Structure Unit := unitStructure bits
  letI : Unit ⊨ T := unit_models_T bits
  letI : (constantsOn Empty).Structure Unit :=
    constantsOn.structure (fun e : Empty => (e.elim : Unit))
  exact inferInstance

/-- Membership in the complete type of an explicit singleton model is
exactly satisfaction of an arbitrary first-order sentence in that model. -/
theorem mem_encode_iff (bits : ℕ → Bool) (φ : L[[Empty]].Sentence) :
    φ ∈ encode bits ↔
    @FirstOrder.Language.Sentence.Realize L[[Empty]] Unit
      (expandedUnitStructure bits) φ := by
  letI : L.Structure Unit := unitStructure bits
  letI : (constantsOn Empty).Structure Unit :=
    constantsOn.structure (fun e : Empty => (e.elim : Unit))
  letI : L[[Empty]].Structure Unit := inferInstance
  change φ ∈ T.typeOf (fun e : Empty => (e.elim : Unit)) ↔ Unit ⊨ φ
  rw [FirstOrder.Language.Theory.CompleteType.mem_typeOf]
  exact FirstOrder.Language.Formula.realize_equivSentence_symm
    Unit φ (fun e : Empty => (e.elim : Unit))

/-- Every complete first-order type is realized by the model of a Boolean
stream. This establishes surjectivity independently of explicit QE. -/
theorem encode_surjective : Function.Surjective encode := by
  classical
  intro p
  let MP : p.toTheory.ModelType := (p.isMaximal.1).some
  let M : Type := MP.Carrier
  letI : L[[Empty]].Structure M := MP.struc
  letI : Nonempty M := MP.nonempty'
  letI : M ⊨ p.toTheory := MP.is_model
  letI : M ⊨ (L.lhomWithConstants Empty).onTheory T :=
    (inferInstance : M ⊨ p.toTheory).mono p.subset
  letI : L.Structure M := (L.lhomWithConstants Empty).reduct M
  let bits := modelBits M
  letI : L.Structure Unit := unitStructure bits
  letI : (constantsOn Empty).Structure Unit :=
    constantsOn.structure (fun e : Empty => (e.elim : Unit))
  letI : L[[Empty]].Structure Unit := expandedUnitStructure bits
  have hiso : M ≃[L[[Empty]]] Unit := expandedModelIsoUnit M
  have hp (φ : L[[Empty]].Sentence) : φ ∈ p ↔ M ⊨ φ := by
    constructor
    · intro hφ
      exact FirstOrder.Language.Theory.realize_sentence_of_mem p.toTheory hφ
    · intro hφ
      cases p.mem_or_not_mem φ with
      | inl hmem => exact hmem
      | inr hneg =>
          have hn : M ⊨ φ.not :=
            FirstOrder.Language.Theory.realize_sentence_of_mem p.toTheory hneg
          exact False.elim
            ((FirstOrder.Language.Sentence.realize_not (M := M)).mp hn hφ)
  refine ⟨bits, ?_⟩
  apply SetLike.ext
  intro φ
  calc
    φ ∈ encode bits ↔ Unit ⊨ φ := mem_encode_iff bits φ
    _ ↔ M ⊨ φ :=
      (FirstOrder.Language.StrongHomClass.realize_sentence hiso φ).symm
    _ ↔ φ ∈ p := (hp φ).symm

theorem encode_bijective : Function.Bijective encode :=
  ⟨encode_injective, encode_surjective⟩

/-- The earlier decode left inverse becomes a two-sided inverse. -/
theorem encode_decode (p : T.CompleteType Empty) :
    encode (decode p) = p := by
  obtain ⟨bits, rfl⟩ := encode_surjective p
  rw [decode_encode]

end Neoplatonic.LTR.Nullary
