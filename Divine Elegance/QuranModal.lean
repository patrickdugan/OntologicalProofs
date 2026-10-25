/-!
Qur'an ikhtilaf v0.8: Ibn 'Arabi / Mulla Sadra inspired modal model.
Lean 4 core, no mathlib, no 'sorry'/'admit' and no empirical axioms.

Interpretation-worlds, not historical alternate universes.  Philosophical
positions are used to MOTIVATE predicates; the historical premises are never
presented as theorems. See README for the philological evidence obligations.

Check: lean QuranModal.lean
-/
import Init

namespace QuranModal

universe u v

/-! Kripke/evidence semantics. -/

abbrev Formula (W : Type u) := W → Prop

def Box {W : Type u} (R : W → W → Prop) (p : Formula W) : Formula W :=
  fun w => ∀ v, R w v → p v

def Diamond {W : Type u} (R : W → W → Prop) (p : Formula W) : Formula W :=
  fun w => ∃ v, R w v ∧ p v

/-- If new evidence removes admissible readings, previous necessities persist. -/
theorem box_refinement {W : Type u} (older newer : W → W → Prop)
    (subset : ∀ a b, newer a b → older a b) (p : Formula W) (w : W)
    (h : Box older p w) : Box newer p w := by
  intro v hv
  exact h v (subset w v hv)

/-- Refinement can remove possibilities. Every surviving possibility was present. -/
theorem diamond_refinement {W : Type u} (older newer : W → W → Prop)
    (subset : ∀ a b, newer a b → older a b) (p : Formula W) (w : W)
    (h : Diamond newer p w) : Diamond older p w := by
  obtain ⟨v, hv, hp⟩ := h
  exact ⟨v, subset w v hv, hp⟩

/-- An admissible counter-reading blocks a necessary conclusion. -/
theorem not_box_of_diamond_counterexample {W : Type u}
    (R : W → W → Prop) (p : Formula W) (w : W)
    (h : Diamond R (fun v => ¬ p v) w) : ¬ Box R p w := by
  intro hb
  obtain ⟨v, hv, hnot⟩ := h
  exact hnot (hb v hv)

/-! Q 2:62/5:69 and Q 3:85, with careful attention to 'seeks'. -/

structure Salvation (P : Type u) where
  /-- Meets the condition in Q 2:62/5:69, including the named group. -/
  Good : P → Prop
  /-- A proposed extension of al-islam as a category. -/
  Islam : P → Prop
  /-- Actively seeks a din other than al-islam (Q 3:85). -/
  SeeksOther : P → Prop
  Reward : P → Prop
  Accepted : P → Prop

def Q262 {P : Type u} (m : Salvation P) : Prop :=
  ∀ p, m.Good p → m.Reward p

def Q385 {P : Type u} (m : Salvation P) : Prop :=
  ∀ p, m.SeeksOther p → ¬ m.Accepted p

/-- This bridge is defensible but is not a verbatim Qur'anic equation. -/
def RewardBridge {P : Type u} (m : Salvation P) : Prop :=
  ∀ p, m.Reward p → m.Accepted p

def Coherent {P : Type u} (m : Salvation P) : Prop :=
  Q262 m ∧ Q385 m ∧ RewardBridge m

/-- Exact set-theoretic consequence of the *literal* two conditionals. -/
theorem eligible_does_not_seek_other {P : Type u} (m : Salvation P)
    (h : Coherent m) : ∀ p, m.Good p → ¬ m.SeeksOther p := by
  intro p hg hs
  have hr : m.Reward p := h.1 p hg
  have ha : m.Accepted p := h.2.2 p hr
  exact (h.2.1 p hs) ha

/-- A *stronger* inclusion follows only if non-Islam entails seeking other. -/
theorem inclusion_requires_exhaustion {P : Type u} (m : Salvation P)
    (h : Coherent m) (partition : ∀ p, ¬ m.Islam p → m.SeeksOther p) :
    ∀ p, m.Good p → m.Islam p := by
  classical
  intro p hg
  by_contra hni
  exact (eligible_does_not_seek_other m h p hg) (partition p hni)

/-- An explicit countermodel to a forced G subset I conclusion. -/
def openCase : Salvation Unit where
  Good := fun _ => True
  Islam := fun _ => False
  SeeksOther := fun _ => False
  Reward := fun _ => True
  Accepted := fun _ => True

theorem openCase_coherent : Coherent openCase := by
  constructor
  · intro _ _
    exact True.intro
  constructor
  · intro _ hs
    exact False.elim hs
  · intro _ _
    exact True.intro

/-- Both verses and the reward bridge can hold with G and not-I. -/
/-- Even a proposed one-way semantic connection is satisfied by the
countermodel.  The controversial *reverse* direction is what forces I. -/
theorem openCase_seeking_excludes_islam :
    ∀ p : Unit, openCase.SeeksOther p → ¬ openCase.Islam p := by
  intro _ hs
  exact False.elim hs

theorem no_forced_membership :
    ¬ (∀ p : Unit, openCase.Good p → openCase.Islam p) := by
  intro h
  exact (h () True.intro)

/-- A generic theorem for conditionals: an acceptance model exists iff the
reward-qualified and active-other sets are disjoint. 'Islam' is irrelevant
until a bridging interpretation is explicitly supplied. -/
theorem salvation_sat_iff_disjoint {P : Type u}
    (Good SeeksOther : P → Prop) :
    (∃ (Reward Accepted : P → Prop),
      (∀ p, Good p → Reward p) ∧
      (∀ p, SeeksOther p → ¬ Accepted p) ∧
      (∀ p, Reward p → Accepted p)) ↔
    (∀ p, Good p → ¬ SeeksOther p) := by
  constructor
  · intro h
    obtain ⟨Reward, Accepted, h1, h2, h3⟩ := h
    intro p hg hs
    exact (h2 p hs) (h3 p (h1 p hg))
  · intro h
    refine ⟨Good, Good, ?_, ?_, ?_⟩
    · intro p hg
      exact hg
    · intro p hs hg
      exact (h p hg) hs
    · intro p hg
      exact hg

/-! Explicit Kripke worlds: an outward social identity alone underdetermines
qualification, inward response, and reward. Every world below is coherent. -/

inductive Reading where
  | outwardButIncluded
  | excludedOnConditions
  | internallyIncluded
  deriving DecidableEq, Repr

def readingModel : Reading → Salvation Unit
  | .outwardButIncluded => openCase
  | .excludedOnConditions => {
      Good := fun _ => False
      Islam := fun _ => False
      SeeksOther := fun _ => True
      Reward := fun _ => False
      Accepted := fun _ => False
    }
  | .internallyIncluded => {
      Good := fun _ => True
      Islam := fun _ => True
      SeeksOther := fun _ => False
      Reward := fun _ => True
      Accepted := fun _ => True
    }

theorem all_readings_coherent (r : Reading) : Coherent (readingModel r) := by
  cases r with
  | outwardButIncluded => exact openCase_coherent
  | excludedOnConditions =>
      constructor
      · intro _ hg
        exact False.elim hg
      constructor
      · intro _ _ ha
        exact ha
      · intro _ hr
        exact False.elim hr
  | internallyIncluded =>
      constructor
      · intro _ _
        exact True.intro
      constructor
      · intro _ hs
        exact False.elim hs
      · intro _ _
        exact True.intro

def AnyReading (_ _ : Reading) : Prop := True

def GetsReward (r : Reading) : Prop := (readingModel r).Reward ()

/-- A reward is possible across admissible interpretive readings. -/
theorem possible_reward :
    Diamond AnyReading GetsReward .outwardButIncluded := by
  exact ⟨.outwardButIncluded, True.intro, True.intro⟩

/-- Its absence is possible too, though all reading-models are coherent. -/
theorem possible_no_reward :
    Diamond AnyReading (fun r => ¬ GetsReward r) .outwardButIncluded := by
  refine ⟨.excludedOnConditions, True.intro, ?_⟩
  intro h
  exact h

/-- All admissible interpretation-worlds are individually consistent. -/
theorem necessarily_coherent :
    Box AnyReading (fun r => Coherent (readingModel r))
      .outwardButIncluded := by
  intro r _
  exact all_readings_coherent r

/-- The text-plus-bridge does not select one person's fate. -/
theorem reward_is_not_necessary :
    ¬ Box AnyReading GetsReward .outwardButIncluded :=
  not_box_of_diamond_counterexample AnyReading GetsReward
    .outwardButIncluded possible_no_reward

/-! A Sadra-inspired (NOT attributed as his exact thesis) discipline: a
higher interpretive disclosure is admitted only with the lower commitment
preserved. This is an *extra* interpretation policy, not an Arabic theorem. -/

structure PreservedLayer (W : Type u) where
  Zahir : W → Prop
  Batin : W → Prop
  respects : ∀ w, Batin w → Zahir w

theorem esoteric_cannot_erase_literal {W : Type u}
    (l : PreservedLayer W) (w : W) :
    ¬ (l.Batin w ∧ ¬ l.Zahir w) := by
  intro h
  exact h.2 (l.respects w h.1)

/-- Evidentially indexed fidelity. Additional genuinely accessible truths
can increase responsibility; a person responsive to all accessible truths
at the stronger state is responsive at the weaker state. -/
def FaithfulAt {P : Type u} {F : Type v}
    (Accessible Answered : P → F → Prop) (p : P) : Prop :=
  ∀ f, Accessible p f → Answered p f

theorem faithful_under_less_evidence {P : Type u} {F : Type v}
    (small large Answered : P → F → Prop)
    (scope : ∀ p f, small p f → large p f) (p : P)
    (h : FaithfulAt large Answered p) : FaithfulAt small Answered p := by
  intro f hs
  exact h f (scope p f hs)

/-- A numeral standing for a degree of realization is not itself a proof
of a particular afterlife verdict. This prevents a Sadrian ontology from
being silently turned into a binary salvation oracle. -/
structure GradedSoul where
  realization : Nat
  rescued : Bool

theorem existential_high_grade_without_assigned_rescue :
    ∃ s : GradedSoul, s.realization = 10 ∧ s.rescued = false := by
  exact ⟨⟨10, false⟩, rfl, rfl⟩

/-! The other two v0.7 clusters: consistency witnesses, conditional on a
chosen distinction between interrogative PURPOSE and causal GUILT. -/

inductive QuestionPurpose where
  | discovery
  | reckoning

/-- Illustrative model, not an assertion that Q 55:39 uniquely means this. -/
def Asked : QuestionPurpose → Prop
  | .discovery => False
  | .reckoning => True

theorem judgment_modes_can_coexist : ¬ Asked .discovery ∧ Asked .reckoning := by
  constructor
  · intro h
    exact h
  · exact True.intro

inductive Agent where
  | inciter
  | actor

inductive Harm where
  | wrongdoing

/-- Distinct persons may be culpable for one harmful event. -/
def Responsible : Agent → Harm → Prop
  | .inciter, .wrongdoing => True
  | .actor, .wrongdoing => True

/-- Transfer of one person's guilt is a different relation. -/
def TransfersGuilt (_ _ : Agent) (_ : Harm) : Prop := False

theorem joint_causal_guilt_without_transfer :
    Responsible .inciter .wrongdoing ∧
    Responsible .actor .wrongdoing ∧
    ¬ TransfersGuilt .actor .inciter .wrongdoing := by
  constructor
  · exact True.intro
  constructor
  · exact True.intro
  · intro h
    exact h

/-! Crucial global coherence warning. Each separate claim has an
admissible reading; NO one reading satisfies both simultaneously. -/

inductive Claim where
  | first
  | second

def Fits : Reading → Claim → Prop
  | .outwardButIncluded, .first => True
  | .excludedOnConditions, .second => True
  | _, _ => False

theorem local_satisfiability_not_global :
    (∀ c : Claim, ∃ r : Reading, Fits r c) ∧
    ¬ (∃ r : Reading, ∀ c : Claim, Fits r c) := by
  constructor
  · intro c
    cases c with
    | first => exact ⟨.outwardButIncluded, True.intro⟩
    | second => exact ⟨.excludedOnConditions, True.intro⟩
  · intro h
    obtain ⟨r, hall⟩ := h
    cases r with
    | outwardButIncluded => exact hall .second
    | excludedOnConditions => exact hall .first
    | internallyIncluded => exact hall .first

end QuranModal
