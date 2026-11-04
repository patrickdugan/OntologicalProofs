import Neoplatonic.LTR.MorphospaceGoal
import Mathlib

/-!
# MOR-04: canonical minimal quotient for future-goal observations

The quotient identifies precisely those states that have identical goal
readouts after every finite permitted action word. This is the standard
deterministic Moore/Myhill-Nerode construction recast for an explicit
goal-interface contract. No novelty is claimed for automaton minimization.

No theological predicate, axiom of nonphysical causation, or assertion
of subjective experience enters the definitions or theorems.
-/

namespace Neoplatonic.LTR.Morphospace

universe u v w
variable {S : Type u} {A : Type v} {Z : Type w}

/-- Two microstates agree on all future goal observations after every
finite action schedule, including the empty schedule. -/
def futureGoalRel (F : A → S → S) (goal : S → Bool) (s t : S) : Prop :=
  ∀ word : List A, goal (runSteps F word s) = goal (runSteps F word t)

theorem futureGoalRel_refl (F : A → S → S) (goal : S → Bool) (s : S) :
    futureGoalRel F goal s s := by
  intro word
  rfl

theorem futureGoalRel_symm (F : A → S → S) (goal : S → Bool)
    {s t : S} (h : futureGoalRel F goal s t) :
    futureGoalRel F goal t s := by
  intro word
  exact (h word).symm

theorem futureGoalRel_trans (F : A → S → S) (goal : S → Bool)
    {s t r : S} (hst : futureGoalRel F goal s t)
    (htr : futureGoalRel F goal t r) :
    futureGoalRel F goal s r := by
  intro word
  exact (hst word).trans (htr word)

/-- The goal-observational future relation is an equivalence. -/
def futureGoalSetoid (F : A → S → S) (goal : S → Bool) : Setoid S where
  r := futureGoalRel F goal
  iseqv := ⟨futureGoalRel_refl F goal,
            (fun _ _ h => futureGoalRel_symm F goal h),
            (fun _ _ _ h₁ h₂ => futureGoalRel_trans F goal h₁ h₂)⟩

/-- The empty schedule gives a well-defined current-goal readout. -/
theorem futureGoalRel_present (F : A → S → S) (goal : S → Bool)
    {s t : S} (h : futureGoalRel F goal s t) :
    goal s = goal t := by
  simpa only [runSteps] using h []

/-- Action congruence: prepending an action preserves future equivalence. -/
theorem futureGoalRel_step (F : A → S → S) (goal : S → Bool)
    (a : A) {s t : S} (h : futureGoalRel F goal s t) :
    futureGoalRel F goal (F a s) (F a t) := by
  intro word
  exact h (a :: word)

/-- The canonical quotient carries a well-defined macro action family. -/
def quotientGoalStep (F : A → S → S) (goal : S → Bool) (a : A) :
    Quotient (futureGoalSetoid F goal) →
      Quotient (futureGoalSetoid F goal) :=
  Quotient.map (F a) (by
    intro s t h
    exact futureGoalRel_step F goal a h)

/-- The canonical quotient retains a well-defined Boolean goal readout. -/
def quotientGoalReadout (F : A → S → S) (goal : S → Bool) :
    Quotient (futureGoalSetoid F goal) → Bool :=
  Quotient.lift goal (by
    intro s t h
    exact futureGoalRel_present F goal h)

/-- Projection of a micro action equals the induced macro action. -/
theorem quotientGoalStep_sound (F : A → S → S) (goal : S → Bool)
    (a : A) (s : S) :
    (Quotient.mk (futureGoalSetoid F goal) (F a s)) =
      quotientGoalStep F goal a
        (Quotient.mk (futureGoalSetoid F goal) s) := by
  rfl

/-- The quotient's goal readout equals the original goal. -/
theorem quotientGoalReadout_sound (F : A → S → S) (goal : S → Bool)
    (s : S) :
    quotientGoalReadout F goal
      (Quotient.mk (futureGoalSetoid F goal) s) = goal s := by
  rfl

/-- Every exact goal-visible macro partition is finer than the
canonical future-goal quotient: states in the same macro fibre must
have identical goal observations after every action word. -/
theorem futureGoalRel_of_exact_macro
    (F : A → S → S) (G : A → Z → Z)
    (goal : S → Bool) (macroGoal : Z → Bool) (p : S → Z)
    (hStep : ∀ a s, p (F a s) = G a (p s))
    (hGoal : ∀ s, goal s = macroGoal (p s))
    {s t : S} (hst : p s = p t) :
    futureGoalRel F goal s t := by
  intro word
  calc
    goal (runSteps F word s) =
        macroGoal (p (runSteps F word s)) := hGoal _
    _ = macroGoal (runSteps G word (p s)) := by
      rw [runSteps_projection p F G hStep word s]
    _ = macroGoal (runSteps G word (p t)) := by rw [hst]
    _ = macroGoal (p (runSteps F word t)) := by
      rw [runSteps_projection p F G hStep word t]
    _ = goal (runSteps F word t) := (hGoal _).symm

/-- A distinguishing goal action word is a certificate that an exact
goal-preserving macrostate encoder must retain two different labels. -/
theorem distinct_macro_of_goal_witness
    (F : A → S → S) (G : A → Z → Z)
    (goal : S → Bool) (macroGoal : Z → Bool) (p : S → Z)
    (hStep : ∀ a s, p (F a s) = G a (p s))
    (hGoal : ∀ s, goal s = macroGoal (p s))
    {s t : S} (word : List A)
    (hDifferent :
      goal (runSteps F word s) ≠ goal (runSteps F word t)) :
    p s ≠ p t := by
  intro hst
  exact hDifferent ((futureGoalRel_of_exact_macro F G goal macroGoal p
    hStep hGoal hst) word)

end Neoplatonic.LTR.Morphospace
