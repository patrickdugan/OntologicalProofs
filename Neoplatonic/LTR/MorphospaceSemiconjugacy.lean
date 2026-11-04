import Mathlib

/-!
# Controlled semiconjugacy: transport of finite action histories

Self-contained structural lemma for the Logos–Topos research program.
The result concerns arbitrary sets, maps, and action lists. It does not
postulate an ontologically separate space of forms or any theological axiom.

Formal compilation has to be verified by the repository's Lean v4.35.0 CI;
this file is submitted as a reviewable draft.
-/

namespace Neoplatonic.LTR.Morphospace

universe u v w

variable {S : Type u} {Z : Type v} {A : Type w}

/-- Apply a finite sequence of actions, first action first. -/
def runSteps (F : A → S → S) : List A → S → S
  | [], s => s
  | a :: rest, s => runSteps F rest (F a s)

/-- All finite action words commute with a common state projection when
every single action does. The projection need not be injective. -/
theorem runSteps_projection
    (p : S → Z) (F : A → S → S) (G : A → Z → Z)
    (commute : ∀ a s, p (F a s) = G a (p s))
    (actions : List A) (s : S) :
    p (runSteps F actions s) = runSteps G actions (p s) := by
  induction actions generalizing s with
  | nil => rfl
  | cons a rest ih =>
      simp only [runSteps]
      calc
        p (runSteps F rest (F a s)) =
            runSteps G rest (p (F a s)) := ih (F a s)
        _ = runSteps G rest (G a (p s)) := by rw [commute]

/-- Every macro-target predicate agrees after a shared action schedule.
This is a pathwise endpoint statement; an external quantified hitting-time
corollary may be derived from all prefixes of a schedule. -/
theorem target_event_projection
    (p : S → Z) (F : A → S → S) (G : A → Z → Z)
    (commute : ∀ a s, p (F a s) = G a (p s))
    (target : Z → Prop) (actions : List A) (s : S) :
    target (p (runSteps F actions s)) ↔
      target (runSteps G actions (p s)) := by
  rw [runSteps_projection p F G commute actions s]

end Neoplatonic.LTR.Morphospace
