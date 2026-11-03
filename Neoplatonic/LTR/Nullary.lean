import Mathlib.ModelTheory.Topology.Types
import Neoplatonic.LTR.TheoryMaps

/-!
# A one-axiom first-order theory with countably many nullary predicates

The language has P_n (n : Nat) at arity zero, no positive-arity
relations, and no functions. Its single nonlogical axiom says that
the domain has at most one element. First-order structures are nonempty,
so every model has exactly one element.

Every Boolean stream b supplies an explicit one-element model whose
predicate P_n holds exactly when b(n) is true. The language map rename σ
is an actual mathlib FirstOrder.Language.LHom.

The canonical complete type of a one-element model will be used to
realize these streams as points of a first-order completion space.
-/

namespace Neoplatonic.LTR.Nullary

open FirstOrder
open FirstOrder.Language

/-- Relation symbols: independent nullary predicates indexed by naturals. -/
def relations : ℕ → Type
  | 0 => ℕ
  | _ + 1 => Empty

/-- A countable first-order language consisting only of nullary relations. -/
def L : FirstOrder.Language where
  Functions := fun _ => Empty
  Relations := relations

/-- The n-th nullary relation symbol, with explicit type ascription. -/
def predSym (n : ℕ) : L.Relations 0 := by
  change ℕ
  exact n

/-- A concrete sentence naming the n-th nullary relation. -/
def atom (n : ℕ) : L.Sentence :=
  FirstOrder.Language.Relations.formula (L := L) (α := Empty)
    (predSym n) (fun i : Fin 0 => Fin.elim0 i)

/-- Exactly one nonlogical axiom: there are no two distinct individuals. -/
def T : L.Theory := { (FirstOrder.Language.Sentence.cardGe L 2).not }

theorem finite_axioms : Set.Finite T :=
  Set.finite_singleton _

/-- Each Boolean sequence determines a model on the one-element domain. -/
@[instance_reducible]
def unitStructure (bits : ℕ → Bool) : L.Structure Unit where
  funMap := fun {n} f _ => nomatch f
  RelMap := fun {n} r _ =>
    match n, r with
    | 0, k => bits k = true
    | _ + 1, r => nomatch r

theorem unit_realizes_atom (bits : ℕ → Bool) (n : ℕ) :
    (letI : L.Structure Unit := unitStructure bits
     Unit ⊨ atom n) ↔ bits n = true := by
  letI : L.Structure Unit := unitStructure bits
  simp [atom, unitStructure, L, relations]

theorem unit_models_T (bits : ℕ → Bool) :
    (letI : L.Structure Unit := unitStructure bits
     Unit ⊨ T) := by
  letI : L.Structure Unit := unitStructure bits
  simp [T]

/-- Each Boolean assignment gives a genuine complete first-order type. -/
noncomputable def encode (bits : ℕ → Bool) : T.CompleteType Empty := by
  letI : L.Structure Unit := unitStructure bits
  letI : Unit ⊨ T := unit_models_T bits
  exact T.typeOf (fun e : Empty => (e.elim : Unit))

/-- Syntactic substitution P_n -> P_(σ n), acting on all formulas. -/
def rename (σ : ℕ → ℕ) : L →ᴸ L where
  onFunction := fun {n} f => nomatch f
  onRelation := fun {n} r =>
    match n, r with
    | 0, k => σ k
    | _ + 1, r => nomatch r

/-- The action on atomic sentences is a literal syntactic equality. -/
theorem rename_atom (σ : ℕ → ℕ) (n : ℕ) :
    (rename σ).onSentence (atom n) = atom (σ n) := by
  simp [atom, predSym, rename, FirstOrder.Language.Relations.formula,
    FirstOrder.Language.LHom.onSentence, FirstOrder.Language.LHom.onFormula,
    FirstOrder.Language.LHom.onBoundedFormula, L, relations]

end Neoplatonic.LTR.Nullary
