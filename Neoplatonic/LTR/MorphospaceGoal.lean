import Neoplatonic.LTR.MorphospaceMinimax
import Mathlib

/-!
# MOR-03: goal observability and action-prefix recovery preservation

A quotient of controlled dynamics preserves a chosen goal exactly only when
the goal readout is constant on the quotient's fibres. These are elementary
statements on sets, functions and finite action schedules.
-/

namespace Neoplatonic.LTR.Morphospace

universe u v w
variable {S : Type u} {Z : Type v} {A : Type w}

/-- The micro goal admits a unique exact macro readout in a surjective
quotient iff it cannot distinguish microstates with the same macrostate. -/
theorem goal_readout_exists_iff_fibre_constant
    (p : S → Z) (hp : Function.Surjective p) (goal : S → Bool) :
    (∃ macroGoal : Z → Bool, ∀ s, goal s = macroGoal (p s)) ↔
      (∀ s t, p s = p t → goal s = goal t) := by
  constructor
  · rintro ⟨macroGoal, hGoal⟩ s t hst
    calc
      goal s = macroGoal (p s) := hGoal s
      _ = macroGoal (p t) := by rw [hst]
      _ = goal t := (hGoal t).symm
  · intro h
    let sec : Z → S := fun z => Classical.choose (hp z)
    refine ⟨fun z => goal (sec z), ?_⟩
    intro s
    exact h s (sec (p s)) (Classical.choose_spec (hp (p s))).symm

/-- A semiconjugacy preserves every endpoint event, and hence the
existence of a goal-reaching action prefix in any finite schedule. -/
theorem macro_goal_hit_prefix_iff
    (p : S → Z) (F : A → S → S) (G : A → Z → Z)
    (hStep : ∀ a s, p (F a s) = G a (p s))
    (goal : Z → Prop) (actions : List A) (s : S) :
    (∃ pre post : List A,
      pre ++ post = actions ∧ goal (p (runSteps F pre s))) ↔
    (∃ pre post : List A,
      pre ++ post = actions ∧ goal (runSteps G pre (p s))) := by
  constructor
  · rintro ⟨pre, post, hconcat, hhit⟩
    refine ⟨pre, post, hconcat, ?_⟩
    rw [runSteps_projection p F G hStep pre s] at hhit
    exact hhit
  · rintro ⟨pre, post, hconcat, hhit⟩
    refine ⟨pre, post, hconcat, ?_⟩
    rw [runSteps_projection p F G hStep pre s]
    exact hhit

/-- A goal observable on the micro system, factored through p, has
the same finite-schedule hit event in the macro system. -/
theorem micro_goal_hit_prefix_iff
    (p : S → Z) (F : A → S → S) (G : A → Z → Z)
    (hStep : ∀ a s, p (F a s) = G a (p s))
    (goalS : S → Bool) (goalZ : Z → Bool)
    (hGoal : ∀ s, goalS s = goalZ (p s))
    (actions : List A) (s : S) :
    (∃ pre post : List A,
      pre ++ post = actions ∧ goalS (runSteps F pre s) = true) ↔
    (∃ pre post : List A,
      pre ++ post = actions ∧ goalZ (runSteps G pre (p s)) = true) := by
  constructor
  · rintro ⟨pre, post, hconcat, hhit⟩
    refine ⟨pre, post, hconcat, ?_⟩
    have hEq : goalS (runSteps F pre s) =
        goalZ (runSteps G pre (p s)) := by
      rw [hGoal (runSteps F pre s), runSteps_projection p F G hStep pre s]
    rwa [hEq] at hhit
  · rintro ⟨pre, post, hconcat, hhit⟩
    refine ⟨pre, post, hconcat, ?_⟩
    have hEq : goalS (runSteps F pre s) =
        goalZ (runSteps G pre (p s)) := by
      rw [hGoal (runSteps F pre s), runSteps_projection p F G hStep pre s]
    rwa [hEq]

end Neoplatonic.LTR.Morphospace
