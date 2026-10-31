import Neoplatonic.LocalConfluence
import MoralRealism.Kernel
import Mathlib.Tactic

namespace MoralRealism
open Neoplatonic
universe u v w

/-- An explicit normative premise. Its independent justification remains open. -/
def ValueBridge {X : Type u} (ground : ConfluentGroundTheory X)
    (good : X → Prop) : Prop :=
  ∀ g, FirstPrinciple ground.prior g → good g

theorem grounded_value {X : Type u} (ground : ConfluentGroundTheory X)
    (seed : X) (good : X → Prop) (bridge : ValueBridge ground good) :
    ∃! g, FirstPrinciple ground.prior g ∧ good g := by
  obtain ⟨g, hg, unique⟩ := confluent_unique_first_principle ground seed
  exact ⟨g, ⟨hg, bridge g hg⟩, fun x hx => unique x hx.1⟩

/-- A nonempty model of the actual grounding axioms, with arbitrary valuation. -/
def unitGround : ConfluentGroundTheory Unit where
  prior := fun _ _ => False
  wf := ⟨fun x => Acc.intro x (fun _ h => False.elim h)⟩
  commonEffect := by
    intro x y
    cases x
    cases y
    exact ⟨(), Reach.refl (), Reach.refl ()⟩
  localCoherence := by
    intro x y z h
    exact False.elim h

theorem ground_with_empty_value :
    (∃! g, FirstPrinciple unitGround.prior g) ∧
    ¬ ValueBridge unitGround (fun _ => False) := by
  have root := confluent_unique_first_principle unitGround ()
  refine ⟨root, ?_⟩
  intro bridge
  obtain ⟨g, hg, _⟩ := root
  exact bridge g hg

/-- A qualitative motivational bridge: every lawful choice beats every violation.
Feasibility and global maximization are additional, explicit premises. -/
theorem maximizer_lawful {A : Type u} (lawful : A → Prop)
    (score : A → ℤ) (chosen : A) (feasible : ∃ a, lawful a)
    (priority : ∀ good bad, lawful good → ¬ lawful bad → score bad < score good)
    (maximizes : ∀ a, score a ≤ score chosen) : lawful chosen := by
  by_contra violation
  obtain ⟨good, hg⟩ := feasible
  exact (not_lt_of_ge (maximizes good)) (priority good chosen hg violation)

/-- Bayes' update raises an interior prior exactly when the likelihood ratio
favors the claim. Calibration of these likelihoods is an external obligation. -/
theorem guidance_update_increases (p hit falseAlarm : ℚ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hh : 0 ≤ hit) (hf : 0 ≤ falseAlarm)
    (positiveEvidence : 0 < p * hit + (1 - p) * falseAlarm) :
    p < (p * hit) / (p * hit + (1 - p) * falseAlarm) ↔ falseAlarm < hit := by
  rw [lt_div_iff₀ positiveEvidence]
  constructor
  · intro h
    by_contra hnot
    have hle : hit ≤ falseAlarm := le_of_not_gt hnot
    have hprod : 0 ≤ p * (1 - p) * (falseAlarm - hit) :=
      mul_nonneg (mul_nonneg (le_of_lt hp0) (le_of_lt (sub_pos.mpr hp1)))
        (sub_nonneg.mpr hle)
    nlinarith
  · intro h
    have hprod : 0 < p * (1 - p) * (hit - falseAlarm) :=
      mul_pos (mul_pos hp0 (sub_pos.mpr hp1)) (sub_pos.mpr h)
    nlinarith

/-- Composition consumes a law indexed by the ground, together with an execution
contract for each first principle. The execution contract is the behavioral bridge. -/
theorem joint_source_execution {X : Type u} {S : Type v} {A : Type w}
    (ground : ConfluentGroundTheory X) (seed : X)
    (good : X → Prop) (bridge : ValueBridge ground good)
    (initial invariant : S → Prop) (step : S → A → S → Prop)
    (gate : S → A → Bool) (law : X → S → A → Prop)
    (contracts : ∀ g, FirstPrinciple ground.prior g → good g →
      ExecutionContract initial invariant step gate (law g)) :
    ∃ g, FirstPrinciple ground.prior g ∧ good g ∧
      ∀ s a t, Reachable initial step s → step s a t → law g s a := by
  obtain ⟨g, hg, _⟩ := grounded_value ground seed good bridge
  refine ⟨g, hg.1, hg.2, ?_⟩
  intro s a t reach edge
  exact reachable_effect_lawful initial invariant step gate (law g)
    (contracts g hg.1 hg.2) reach edge

#print axioms grounded_value
#print axioms ground_with_empty_value
#print axioms maximizer_lawful
#print axioms guidance_update_increases
#print axioms joint_source_execution
end MoralRealism
