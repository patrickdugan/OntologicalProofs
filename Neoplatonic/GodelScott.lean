import Neoplatonic.Core

/-!
# Gödel's ontological argument, Scott's version, in Kripke semantics

STATUS: written without a compiler. Every proof below is a worked derivation,
not a checked one. Compile with `lake env lean Neoplatonic/GodelScott.lean`
and fix before trusting anything in this file.

Tags used in comments:
* `[LEAN]`    a theorem: Lean checks that the conclusion follows from the
              fields of the theory structure and the stated frame condition.
* `[PREMISE]` a structure field: a metaphysical assumption a skeptic may reject.
* `[GAP]`     a step not taken here; the conclusion does not reach it.

Semantics: constant domain `α`, worlds `W`, accessibility `R`.
Properties are intensional (`α → W → Prop`). Positivity `P` is world-indexed.
Axioms are stated as validities (at every world). Frame conditions are
hypotheses of individual theorems, never global. They are the core/mathlib
relation classes, passed as explicit hypotheses rather than instances:
`Std.Refl R` (T), `Std.Symm R` (B), `IsTrans W R` (4). (Mathlib removed
`Reflexive`/`Transitive` and deprecated `Symmetric` in their favour.)

Result of this file: the Scott development uses symmetry (B) exactly once,
in `godlike_exists`. Reflexivity and transitivity are never used.
-/

namespace Neoplatonic
namespace Godel

universe u v

section Semantics
variable {W : Type u} (R : W → W → Prop)

/-- `□p` at `w`: `p` holds at every world accessible from `w`. -/
def Box (p : W → Prop) : W → Prop := fun w => ∀ v, R w v → p v

/-- `◇p` at `w`: `p` holds at some world accessible from `w`. -/
def Dia (p : W → Prop) : W → Prop := fun w => ∃ v, R w v ∧ p v

end Semantics

/-- An intensional property. -/
abbrev Property (W : Type u) (α : Type v) := α → W → Prop

/-- Property negation. -/
def pneg {W : Type u} {α : Type v} (φ : Property W α) : Property W α :=
  fun x w => ¬ φ x w

section Definitions
variable {W : Type u} (R : W → W → Prop) {α : Type v}

/-- D1. `G(x) :⟺ ∀φ. P(φ) → φ(x)`. -/
def Godlike (P : Property W α → W → Prop) : Property W α :=
  fun x w => ∀ φ, P φ w → φ x w

/-- D2 (Scott). `φ ess x :⟺ φ(x) ∧ ∀ψ. ψ(x) → □∀y (φ(y) → ψ(y))`.
The first conjunct is Scott's addition; Gödel's 1970 text omits it (`EssenceG`). -/
def Essence (φ : Property W α) : Property W α :=
  fun x w => φ x w ∧
    ∀ ψ : Property W α, ψ x w → Box R (fun v => ∀ y, φ y v → ψ y v) w

/-- D3. `NE(x) :⟺ ∀φ. φ ess x → □∃y φ(y)`. -/
def NecExists : Property W α :=
  fun x w => ∀ φ : Property W α, Essence R φ x w → Box R (fun v => ∃ y, φ y v) w

end Definitions

/-- Scott's axiom set. Every field is a `[PREMISE]`. -/
structure ScottTheory {W : Type u} (R : W → W → Prop) (α : Type v) where
  /-- Positivity, world-indexed. -/
  P : Property W α → W → Prop
  /-- A1. `P(¬φ) ↔ ¬P(φ)`. -/
  A1 : ∀ (w : W) (φ : Property W α), P (pneg φ) w ↔ ¬ P φ w
  /-- A2. `P(φ) ∧ □∀x (φ(x) → ψ(x)) → P(ψ)`. -/
  A2 : ∀ (w : W) (φ ψ : Property W α),
    P φ w → Box R (fun v => ∀ x, φ x v → ψ x v) w → P ψ w
  /-- A3. `P(G)`. -/
  A3 : ∀ w : W, P (Godlike P) w
  /-- A4. `P(φ) → □P(φ)`. -/
  A4 : ∀ (w : W) (φ : Property W α), P φ w → Box R (P φ) w
  /-- A5. `P(NE)`. -/
  A5 : ∀ w : W, P (NecExists R) w

section Theorems
variable {W : Type u} {R : W → W → Prop} {α : Type v}

/-- T1 [LEAN, K]. Shared by Scott, Gödel-1970 and Anderson: needs only the weak
half of A1 (`P(φ) → ¬P(¬φ)`) and A2. -/
theorem positive_possible_of (P : Property W α → W → Prop)
    (A1w : ∀ (w : W) (φ : Property W α), P φ w → ¬ P (pneg φ) w)
    (A2 : ∀ (w : W) (φ ψ : Property W α),
      P φ w → Box R (fun v => ∀ x, φ x v → ψ x v) w → P ψ w)
    (w : W) (φ : Property W α) (h : P φ w) :
    Dia R (fun v => ∃ x, φ x v) w := by
  by_contra hcon
  apply A1w w φ h
  apply A2 w φ (pneg φ) h
  intro v hv x hx _
  exact hcon ⟨v, hv, x, hx⟩

variable (T : ScottTheory R α)

/-- The weak half of A1. -/
theorem ScottTheory.A1w (w : W) (φ : Property W α) (h : T.P φ w) :
    ¬ T.P (pneg φ) w :=
  fun hn => (T.A1 w φ).mp hn h

/-- T1 for Scott [LEAN, K]. -/
theorem positive_possible (w : W) (φ : Property W α) (h : T.P φ w) :
    Dia R (fun v => ∃ x, φ x v) w :=
  positive_possible_of T.P T.A1w T.A2 w φ h

/-- C [LEAN, K]. `◇∃x G(x)`. -/
theorem godlike_possible (w : W) :
    Dia R (fun v => ∃ x, Godlike T.P x v) w :=
  positive_possible T w _ (T.A3 w)

/-- L [LEAN, K]. Every property a God-like being has is positive.
Uses the strong half of A1 (`¬P(φ) → P(¬φ)`). -/
theorem godlike_positive_of_has (w : W) {x : α} (hg : Godlike T.P x w)
    (φ : Property W α) (hφ : φ x w) : T.P φ w := by
  by_contra hn
  exact hg (pneg φ) ((T.A1 w φ).mpr hn) hφ

/-- Positivity is the principal ultrafilter of the God-like being [LEAN, K]:
`P(φ) ↔ φ(g)`. "Positive" has no content independent of its bearer. -/
theorem positive_iff_godlike_has (w : W) {g : α} (hg : Godlike T.P g w)
    (φ : Property W α) : T.P φ w ↔ φ g w :=
  ⟨hg φ, godlike_positive_of_has T w hg φ⟩

/-- T2 [LEAN, K]. `G(x) → G ess x`. Uses L and A4. -/
theorem godlike_essence (w : W) {x : α} (hg : Godlike T.P x w) :
    Essence R (Godlike T.P) x w := by
  refine ⟨hg, ?_⟩
  intro ψ hψ v hv y hy
  exact hy ψ (T.A4 w ψ (godlike_positive_of_has T w hg ψ hψ) v hv)

/-- Monotheism [LEAN, K]. At most one God-like being per world. -/
theorem godlike_unique (w : W) {x y : α}
    (hx : Godlike T.P x w) (hy : Godlike T.P y w) : y = x :=
  hy _ (godlike_positive_of_has T w hx (fun z _ => z = x) rfl)

/-- E [LEAN, KB]. Actual existence. The ONLY use of a frame condition in the
Scott development: symmetry returns from the witness world of C to `w`. -/
theorem godlike_exists (hsymm : Std.Symm R) (w : W) : ∃ x, Godlike T.P x w := by
  obtain ⟨v, hwv, g, hg⟩ := godlike_possible T w
  have hne : NecExists R g v := hg _ (T.A5 v)
  exact hne _ (godlike_essence T v hg) w (hsymm.symm _ _ hwv)

/-- T3 [LEAN, KB]. `□∃x G(x)`. -/
theorem godlike_necessary (hsymm : Std.Symm R) (w : W) :
    Box R (fun v => ∃ x, Godlike T.P x v) w := by
  obtain ⟨g, hg⟩ := godlike_exists T hsymm w
  exact hg _ (T.A5 w) _ (godlike_essence T w hg)

/-- Structural cause of modal collapse [LEAN, K, NO positivity axioms].
Scott's D2 quantifies over all properties, including world-constant `λy. p`.
Any individual with a necessarily instantiated Scott-essence collapses
modality at its world. -/
theorem collapse_of_scott_essence {G : Property W α} {g : α} {w : W}
    (hess : Essence R G g w) (hnec : Box R (fun v => ∃ y, G y v) w)
    (p : W → Prop) (hp : p w) : Box R p w := by
  intro v hv
  obtain ⟨y, hy⟩ := hnec v hv
  exact hess.2 (fun _ u => p u) hp v hv y hy

include T in
/-- Modal collapse [LEAN, KB]. `p → □p` for every proposition.
Instance supplied by T2 (A1 strong half, A4) and T3 (A1, A2, A3, A5, B).
(`include T in`: the statement does not mention `T`, so without it Lean's
variable-inclusion rule would drop `T` from the signature.) -/
theorem modal_collapse (hsymm : Std.Symm R) (w : W) (p : W → Prop) (hp : p w) :
    Box R p w := by
  obtain ⟨g, hg⟩ := godlike_exists T hsymm w
  exact collapse_of_scott_essence (godlike_essence T w hg)
    (godlike_necessary T hsymm w) p hp

end Theorems

section Consistency

/-- Consistency witness [LEAN]: one world, one individual, `P φ := φ(⋆)`.
Without this, `modal_collapse` could be a theorem about an empty theory. -/
def trivialScott : ScottTheory (fun (_ _ : Unit) => True) Unit where
  P := fun φ w => φ () w
  A1 := fun _ _ => Iff.rfl
  A2 := fun w _ _ h hb => hb w trivial () h
  A3 := fun _ _ h => h
  A4 := fun w _ h v _ => by cases w; cases v; exact h
  A5 := fun w _ hess v _ => ⟨(), by cases w; cases v; exact hess.1⟩

theorem scott_consistent :
    Nonempty (ScottTheory (fun (_ _ : Unit) => True) Unit) := ⟨trivialScott⟩

end Consistency

section GodelOriginal
variable {W : Type u} {α : Type v}

/-- D2 as in Gödel's 1970 manuscript, without the conjunct `φ(x)`. -/
def EssenceG (R : W → W → Prop) (φ : Property W α) : Property W α :=
  fun x w => ∀ ψ : Property W α, ψ x w → Box R (fun v => ∀ y, φ y v → ψ y v) w

def NecExistsG (R : W → W → Prop) : Property W α :=
  fun x w => ∀ φ : Property W α, EssenceG R φ x w → Box R (fun v => ∃ y, φ y v) w

/-- Gödel's 1970 axiom set (identical to Scott's except D2/D3). -/
structure GodelTheory (R : W → W → Prop) (α : Type v) where
  P : Property W α → W → Prop
  A1 : ∀ (w : W) (φ : Property W α), P (pneg φ) w ↔ ¬ P φ w
  A2 : ∀ (w : W) (φ ψ : Property W α),
    P φ w → Box R (fun v => ∀ x, φ x v → ψ x v) w → P ψ w
  A3 : ∀ w : W, P (Godlike P) w
  A4 : ∀ (w : W) (φ : Property W α), P φ w → Box R (P φ) w
  A5 : ∀ w : W, P (NecExistsG R) w

/-- [LEAN, KB] Gödel's 1970 axioms are inconsistent
(Benzmüller–Woltzenlogel Paleo 2016): `λy. ⊥` is a Gödel-essence of
everything, so NE forces `□∃y ⊥`. A4 is not used. -/
theorem godel_inconsistent {R : W → W → Prop} (hsymm : Std.Symm R)
    (T : GodelTheory R α) (w : W) : False := by
  obtain ⟨v, hwv, g, hg⟩ :=
    positive_possible_of T.P (fun w φ h hn => (T.A1 w φ).mp hn h) T.A2 w _ (T.A3 w)
  have hne : NecExistsG R g v := hg _ (T.A5 v)
  have hess : EssenceG R (fun _ _ => False) g v := fun _ _ _ _ _ hy => False.elim hy
  obtain ⟨_, hy⟩ := hne _ hess w (hsymm.symm _ _ hwv)
  exact hy

/-- [LEAN, K] The same inconsistency with no frame condition at all. Symmetry
in `godel_inconsistent` only supplies a world accessible from the witness
world `v`; T1 applied to A3 at `v` supplies one already (A1 and A2, as
validities, force every world to have an accessible world). Added during
compilation; not in the handoff. -/
theorem godel_inconsistent_K {R : W → W → Prop} (T : GodelTheory R α) (w : W) :
    False := by
  have A1w : ∀ (w : W) (φ : Property W α), T.P φ w → ¬ T.P (pneg φ) w :=
    fun w φ h hn => (T.A1 w φ).mp hn h
  obtain ⟨v, -, g, hg⟩ := positive_possible_of T.P A1w T.A2 w _ (T.A3 w)
  obtain ⟨u, hvu, -⟩ := positive_possible_of T.P A1w T.A2 v _ (T.A3 v)
  have hne : NecExistsG R g v := hg _ (T.A5 v)
  have hess : EssenceG R (fun _ _ => False) g v := fun _ _ _ _ _ hy => False.elim hy
  obtain ⟨_, hy⟩ := hne _ hess u hvu
  exact hy

end GodelOriginal

end Godel
end Neoplatonic
