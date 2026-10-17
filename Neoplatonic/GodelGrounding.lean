import Neoplatonic.GodelAnderson
import Neoplatonic.LocalConfluence
import Neoplatonic.Modal

/-!
# The ontological argument and the grounding framework are independent

STATUS: unverified; compile and fix.

`Modal.lean` showed with a toy that "exists in every world" does not entail
`Root`. This file makes the same point against the full Scott axiom set and
the full grounding axiom set at once, and identifies the single bridge premise
(A6) under which the two conclusions pick out the same object.

* `godlike_ne_firstPrinciple`  one model satisfies `ScottTheory` and
  `GroundTheory`; its God-like being is `true`, its first principle is `false`.
* `firstPrinciple_not_godlike` the first principle of `natTheory` (0) is not
  God-like under a Scott theory on ℕ.
* `godlike_firstPrinciple`     with A6 (`[PREMISE]`: being ungrounded is
  positive) the God-like being is the first principle.
Neither framework's conclusion entails the other's. They share no premise.
-/

namespace Neoplatonic
namespace Godel

universe u v

section Bridge
variable {W : Type u} {R : W → W → Prop} {α : Type v}

/-- Being ungrounded, as a world-constant intensional property. -/
def RootProp (prior : α → α → Prop) : Property W α := fun x _ => Root prior x

/-- A6 [PREMISE, in neither Gödel nor Scott]: being ungrounded is positive.
Given A6, every God-like being is a root. [LEAN, K] -/
theorem godlike_root (T : ScottTheory R α) (prior : α → α → Prop)
    (hA6 : ∀ w, T.P (RootProp prior) w) (w : W) {x : α}
    (hg : Godlike T.P x w) : Root prior x :=
  hg _ (hA6 w)

/-- With A6 and the grounding axioms, the God-like being is the first principle.
[LEAN] Both frameworks' premises plus A6 are consumed; nothing less suffices. -/
theorem godlike_firstPrinciple (T : ScottTheory R α) (G : GroundTheory α)
    (hA6 : ∀ w, T.P (RootProp G.prior) w) (w : W) {x : α}
    (hg : Godlike T.P x w) : FirstPrinciple G.prior x := by
  obtain ⟨g, hgfp, -⟩ := unique_first_principle G x
  have hroot : Root G.prior x := godlike_root T G.prior hA6 w hg
  have hgx : g = x := ancestor_of_root_eq hroot (hgfp.2 x)
  exact hgx ▸ hgfp

end Bridge

section Independence

/-- Scott's axioms, two individuals, one world; positivity := held by `true`. [LEAN] -/
def groundedScott : ScottTheory (fun (_ _ : Unit) => True) Bool where
  P := fun φ w => φ true w
  A1 := fun _ _ => Iff.rfl
  A2 := fun w _ _ h hb => hb w trivial true h
  A3 := fun _ _ h => h
  A4 := fun w _ h v _ => by cases w; cases v; exact h
  A5 := fun w _ hess v _ => ⟨true, by cases w; cases v; exact hess.1⟩

theorem groundsSecond_wf : WellFounded groundsSecond := by
  have hf : Acc groundsSecond false := ⟨false, fun _ hy => nomatch hy.2⟩
  refine ⟨fun b => ?_⟩
  cases b
  · exact hf
  · exact ⟨true, fun y hy => hy.1 ▸ hf⟩

theorem reach_false_all (b : Bool) : Reach groundsSecond false b := by
  cases b
  · exact Reach.refl false
  · exact Reach.step (Reach.refl false) ⟨rfl, rfl⟩

/-- The grounding axioms hold on the same two beings: `false` grounds `true`. [LEAN] -/
def twoBeingGround : GroundTheory Bool where
  prior := groundsSecond
  wf := groundsSecond_wf
  commonPrior := fun x y => ⟨false, reach_false_all x, reach_false_all y⟩

/-- In one model of both axiom sets, the God-like being (`true`) is necessarily
God-like, is the unique God-like being, and is not a root; the first principle
is `false`. Upgrades `modal_necessity_does_not_imply_ungrounded`. [LEAN] -/
theorem godlike_ne_firstPrinciple :
    Box (fun (_ _ : Unit) => True) (fun v => ∃ x, Godlike groundedScott.P x v) () ∧
    (∀ x, Godlike groundedScott.P x () → x = true) ∧
    FirstPrinciple groundsSecond false ∧
    ¬ Root groundsSecond true :=
  ⟨godlike_necessary groundedScott ⟨fun _ _ _ => trivial⟩ (),
   fun _ hx => godlike_unique groundedScott () (fun _ h => h) hx,
   ⟨(fun ⟨_, hy⟩ => nomatch hy.2), reach_false_all⟩,
   fun hroot => hroot ⟨false, rfl, rfl⟩⟩

/-- Scott's axioms over ℕ, positivity := held by `1`. [LEAN] -/
def natScott : ScottTheory (fun (_ _ : Unit) => True) ℕ where
  P := fun φ w => φ 1 w
  A1 := fun _ _ => Iff.rfl
  A2 := fun w _ _ h hb => hb w trivial 1 h
  A3 := fun _ _ h => h
  A4 := fun w _ h v _ => by cases w; cases v; exact h
  A5 := fun w _ hess v _ => ⟨1, by cases w; cases v; exact hess.1⟩

/-- The first principle of `natTheory` is `0`; it is not God-like. [LEAN] -/
theorem firstPrinciple_not_godlike :
    FirstPrinciple natTheory.prior 0 ∧ ¬ Godlike natScott.P 0 () :=
  ⟨⟨fun ⟨y, hy⟩ => Nat.not_lt_zero y hy, nat_reachable_from_zero⟩,
   fun hg => Nat.zero_ne_one (hg (fun z _ => z = 1) rfl)⟩

end Independence

end Godel
end Neoplatonic
