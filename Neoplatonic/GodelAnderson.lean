import Neoplatonic.GodelScott

/-!
# Anderson's emendation (1990) and the failure of modal collapse

STATUS: unverified; compile and fix.

Anderson changes D1 and D2 to biconditionals about *necessary* properties and
keeps only the weak half of A1. The frame requirement rises from KB to S5;
each theorem's signature lists exactly the frame conditions it consumes:
* `Std.Refl R`   (T): extracting `NE*(g)` from `□NE*(g)`; T2*(→); monotheism*.
* `Std.Symm R`   (B): stability of `P` along `R`; return from the witness world.
* `IsTrans W R`  (4): stability of `□` along `R`, used in T2*(←).

Collapse is blocked because D2* takes `□ψ(x)` as input, not `ψ(x)`:
the world-constant property `λy. p` can no longer be fed `p` alone.
`andersonTwoWorlds` is an S5 model of A1*–A5 in which `p → □p` fails.
-/

namespace Neoplatonic
namespace Godel

universe u v

section Definitions
variable {W : Type u} {α : Type v}

/-- D1*. `G*(x) :⟺ ∀φ. P(φ) ↔ □φ(x)`. -/
def GodlikeA (R : W → W → Prop) (P : Property W α → W → Prop) : Property W α :=
  fun x w => ∀ φ, P φ w ↔ Box R (φ x) w

/-- D2*. `φ ess* x :⟺ ∀ψ. □ψ(x) ↔ □∀y (φ(y) → ψ(y))`. -/
def EssenceA (R : W → W → Prop) (φ : Property W α) : Property W α :=
  fun x w => ∀ ψ : Property W α,
    Box R (ψ x) w ↔ Box R (fun v => ∀ y, φ y v → ψ y v) w

/-- D3*. -/
def NecExistsA (R : W → W → Prop) : Property W α :=
  fun x w => ∀ φ : Property W α, EssenceA R φ x w → Box R (fun v => ∃ y, φ y v) w

end Definitions

/-- Anderson's axiom set. Every field is a `[PREMISE]`. -/
structure AndersonTheory {W : Type u} (R : W → W → Prop) (α : Type v) where
  P : Property W α → W → Prop
  /-- A1*. Only `P(φ) → ¬P(¬φ)`. Indifferent properties are allowed. -/
  A1 : ∀ (w : W) (φ : Property W α), P φ w → ¬ P (pneg φ) w
  A2 : ∀ (w : W) (φ ψ : Property W α),
    P φ w → Box R (fun v => ∀ x, φ x v → ψ x v) w → P ψ w
  A3 : ∀ w : W, P (GodlikeA R P) w
  A4 : ∀ (w : W) (φ : Property W α), P φ w → Box R (P φ) w
  A5 : ∀ w : W, P (NecExistsA R) w

section Theorems
variable {W : Type u} {R : W → W → Prop} {α : Type v} (T : AndersonTheory R α)

/-- C* [LEAN, K]. -/
theorem godlikeA_possible (w : W) :
    Dia R (fun v => ∃ x, GodlikeA R T.P x v) w :=
  positive_possible_of T.P T.A1 T.A2 w _ (T.A3 w)

/-- [LEAN, B] `P` is stable along `R` (A4 both ways). -/
theorem AndersonTheory.P_stable (hsymm : Std.Symm R) {w v : W} (hwv : R w v)
    (φ : Property W α) : T.P φ w ↔ T.P φ v :=
  ⟨fun h => T.A4 w φ h v hwv, fun h => T.A4 v φ h w (hsymm.symm _ _ hwv)⟩

/-- [LEAN, B4] `□` is stable along `R`. -/
theorem box_stable (hsymm : Std.Symm R) (htrans : IsTrans W R)
    {w v : W} (hwv : R w v) (p : W → Prop) : Box R p w ↔ Box R p v :=
  ⟨fun h u hvu => h u (htrans.trans _ _ _ hwv hvu),
   fun h u hwu => h u (htrans.trans _ _ _ (hsymm.symm _ _ hwv) hwu)⟩

/-- [LEAN, B4] God-likeness* is stable along `R`. -/
theorem godlikeA_stable (hsymm : Std.Symm R) (htrans : IsTrans W R)
    {w v : W} (hwv : R w v) {x : α} (hg : GodlikeA R T.P x w) :
    GodlikeA R T.P x v := fun φ =>
  ((T.P_stable hsymm hwv φ).symm.trans (hg φ)).trans (box_stable hsymm htrans hwv _)

/-- T2* [LEAN, S5]. (→) uses T; (←) uses B and 4. -/
theorem godlikeA_essence (hrefl : Std.Refl R) (hsymm : Std.Symm R)
    (htrans : IsTrans W R) (w : W) {x : α} (hg : GodlikeA R T.P x w) :
    EssenceA R (GodlikeA R T.P) x w := by
  intro ψ
  constructor
  · intro hb v hwv y hy
    exact (hy ψ).mp (T.A4 w ψ ((hg ψ).mpr hb) v hwv) v (hrefl.refl v)
  · intro hb v hwv
    exact hb v hwv x (godlikeA_stable T hsymm htrans hwv hg)

/-- E* [LEAN, S5]. -/
theorem godlikeA_exists (hrefl : Std.Refl R) (hsymm : Std.Symm R)
    (htrans : IsTrans W R) (w : W) : ∃ x, GodlikeA R T.P x w := by
  obtain ⟨v, hwv, g, hg⟩ := godlikeA_possible T w
  have hne : NecExistsA R g v := (hg _).mp (T.A5 v) v (hrefl.refl v)
  exact hne _ (godlikeA_essence T hrefl hsymm htrans v hg) w (hsymm.symm _ _ hwv)

/-- T3* [LEAN, S5]. `□∃x G*(x)`. -/
theorem godlikeA_necessary (hrefl : Std.Refl R) (hsymm : Std.Symm R)
    (htrans : IsTrans W R) (w : W) :
    Box R (fun v => ∃ x, GodlikeA R T.P x v) w := by
  obtain ⟨g, hg⟩ := godlikeA_exists T hrefl hsymm htrans w
  exact (hg _).mp (T.A5 w) w (hrefl.refl w) _ (godlikeA_essence T hrefl hsymm htrans w hg)

/-- Monotheism* [LEAN, T]. Survives the emendation. -/
theorem godlikeA_unique (hrefl : Std.Refl R) (w : W) {x y : α}
    (hx : GodlikeA R T.P x w) (hy : GodlikeA R T.P y w) : y = x :=
  (hy _).mp ((hx (fun z _ => z = x)).mpr (fun _ _ => rfl)) w (hrefl.refl w)

end Theorems

section Countermodel

/-- Total accessibility on two worlds: an S5 frame. -/
def totalR : Bool → Bool → Prop := fun _ _ => True

theorem totalR_refl : Std.Refl totalR := ⟨fun _ => trivial⟩
theorem totalR_symm : Std.Symm totalR := ⟨fun _ _ _ => trivial⟩
theorem totalR_trans : IsTrans Bool totalR := ⟨fun _ _ _ _ _ => trivial⟩

/-- Anderson's axioms with one individual and `P φ := □φ(⋆)`. [LEAN] -/
def andersonTwoWorlds : AndersonTheory totalR Unit where
  P := fun φ _ => ∀ v, φ () v
  A1 := fun _ _ h hn => hn true (h true)
  A2 := fun _ _ _ h hb v => hb v trivial () (h v)
  A3 := fun _ _ _ => ⟨fun h u _ => h u, fun h u => h u trivial⟩
  A4 := fun _ _ h _ _ => h
  A5 := fun _ _ φ hess u _ => ⟨(), (hess φ).mpr (fun _ _ _ hy => hy) u trivial⟩

/-- `w = true` holds at `true` and is not necessary there. [LEAN] -/
theorem totalR_no_collapse :
    ¬ ∀ (p : Bool → Prop) (w : Bool), p w → Box totalR p w := by
  intro h
  exact Bool.noConfusion (h (fun w => w = true) true rfl false trivial)

/-- Collapse is not a consequence of Anderson's axioms, even in S5. [LEAN] -/
theorem anderson_no_collapse :
    ∃ (W : Type) (R : W → W → Prop) (α : Type),
      Std.Refl R ∧ Std.Symm R ∧ IsTrans W R ∧
      Nonempty (AndersonTheory R α) ∧
      ¬ ∀ (p : W → Prop) (w : W), p w → Box R p w :=
  ⟨Bool, totalR, Unit, totalR_refl, totalR_symm, totalR_trans,
    ⟨andersonTwoWorlds⟩, totalR_no_collapse⟩

/-- Sanity: Scott's strong A1 fails in the same model, as it must. [LEAN] -/
theorem scott_A1_fails_twoWorlds :
    ¬ ∀ (w : Bool) (φ : Property Bool Unit),
      andersonTwoWorlds.P (pneg φ) w ↔ ¬ andersonTwoWorlds.P φ w := by
  intro h
  have hneg := (h true (fun _ w => w = true)).mpr
    (fun hall => Bool.noConfusion (hall false))
  exact hneg true rfl

end Countermodel

end Godel
end Neoplatonic
