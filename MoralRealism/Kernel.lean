import Init

/-! Finite-agent interfaces and conditional results. Moral predicates are inputs.
See PREMISES.md for the philosophical obligations and CLAIMS.md for scope. -/
namespace MoralRealism
universe u v w

/-- Distinct duties hidden by the same view obstruct every exact decoder. -/
theorem collision_obstruction {X : Type u} {V : Type v} {A : Type w}
    (view : X → V) (duty : X → A) (x y : X)
    (same : view x = view y) (different : duty x ≠ duty y) :
    ¬ ∃ decode : V → A, ∀ z, decode (view z) = duty z := by
  intro h
  obtain ⟨decode, correct⟩ := h
  apply different
  calc
    duty x = decode (view x) := (correct x).symm
    _ = decode (view y) := congrArg decode same
    _ = duty y := correct y

/-- A chosen representative suffices when duty is constant on each view fiber. -/
theorem sufficient_view {X : Type u} {V : Type v} {A : Type w}
    (view : X → V) (duty : X → A) (representative : V → X)
    (covers : ∀ x, view (representative (view x)) = view x)
    (constantOnFibers : ∀ x y, view x = view y → duty x = duty y) :
    ∀ x, duty (representative (view x)) = duty x := by
  intro x
  exact constantOnFibers _ _ (covers x)

/-- Uniform injustice is compatible with every relabeling in this toy domain. -/
theorem symmetry_insufficient :
    ∃ verdict : Bool → Bool,
      (∀ x, verdict (!x) = verdict x) ∧ verdict true = false := by
  exact ⟨fun _ => false, fun _ => rfl, rfl⟩

def fixedDuty (_ : Bool) : Bool := true
def correctJudgment (_ : Bool) : Bool := true
def oversightSensitiveAction (watched : Bool) : Bool := watched

/-- A correctly represented obligation coexists with an observation-dependent policy switch. -/
theorem knowledge_action_countermodel :
    (∀ c, correctJudgment c = fixedDuty c) ∧
    oversightSensitiveAction true = fixedDuty true ∧
    oversightSensitiveAction false ≠ fixedDuty false := by
  decide

/-- Equal observed/unobserved behavior can violate the obligation in both. -/
theorem zero_gap_countermodel :
    ∃ action : Bool → Bool,
      action true = action false ∧ action false ≠ fixedDuty false := by
  exact ⟨fun _ => false, rfl, by decide⟩

/-- Authentication and reliability are supplied separately; evidence must exist. -/
theorem authenticated_guidance {W : Type u}
    (evidence authenticated claim : W → Prop)
    (consistent : ∃ x, evidence x)
    (auth : ∀ x, evidence x → authenticated x)
    (reliable : ∀ x, authenticated x → claim x) :
    (∀ x, evidence x → claim x) ∧ ∃ x, evidence x ∧ claim x := by
  have entails : ∀ x, evidence x → claim x := fun x hx => reliable x (auth x hx)
  obtain ⟨x, hx⟩ := consistent
  exact ⟨entails, x, hx, entails x hx⟩

/-- Refinement retains entailment, with consistency as a separate obligation. -/
theorem consistent_refinement {W : Type u}
    (oldEvidence newEvidence claim : W → Prop)
    (nonempty : ∃ x, newEvidence x)
    (refines : ∀ x, newEvidence x → oldEvidence x)
    (entails : ∀ x, oldEvidence x → claim x) :
    (∃ x, newEvidence x) ∧ (∀ x, newEvidence x → claim x) := by
  exact ⟨nonempty, fun x hx => entails x (refines x hx)⟩

/-- Empty admissible-world sets make every universal claim vacuous. -/
theorem empty_evidence_vacuous {W : Type u} (claim : W → Prop) :
    ∀ x : W, False → claim x := fun _ h => False.elim h

/-- Identical reported guidance is compatible with opposite truth values. -/
theorem report_does_not_authenticate :
    ¬ ∃ decode : Unit → Bool, ∀ truth : Bool, decode () = truth := by
  intro h
  obtain ⟨decode, correct⟩ := h
  have impossible : false = true := (correct false).symm.trans (correct true)
  cases impossible

inductive Reachable {S : Type u} {A : Type v}
    (initial : S → Prop) (step : S → A → S → Prop) : S → Prop where
  | start {s : S} : initial s → Reachable initial step s
  | advance {s t : S} {a : A} :
      Reachable initial step s → step s a t → Reachable initial step t

/-- Initial validity and preservation cover arbitrary finite execution prefixes. -/
theorem reachable_invariant {S : Type u} {A : Type v}
    (initial invariant : S → Prop) (step : S → A → S → Prop)
    (starts : ∀ s, initial s → invariant s)
    (preserves : ∀ s a t, invariant s → step s a t → invariant t) :
    ∀ s, Reachable initial step s → invariant s := by
  intro s hs
  induction hs with
  | start h => exact starts _ h
  | advance _ edge ih => exact preserves _ _ _ ih edge

/-- Complete mediation covers every actual effect, including updates and outputs. -/
structure ExecutionContract {S : Type u} {A : Type v}
    (initial invariant : S → Prop) (step : S → A → S → Prop)
    (gate : S → A → Bool) (lawful : S → A → Prop) : Prop where
  starts : ∀ s, initial s → invariant s
  preserves : ∀ s a t, invariant s → step s a t → invariant t
  mediation : ∀ s a t, step s a t → gate s a = true
  sound : ∀ s a, invariant s → gate s a = true → lawful s a

/-- Every reachable effect satisfies the supplied law under the four premises. -/
theorem reachable_effect_lawful {S : Type u} {A : Type v}
    (initial invariant : S → Prop) (step : S → A → S → Prop)
    (gate : S → A → Bool) (lawful : S → A → Prop)
    (contract : ExecutionContract initial invariant step gate lawful)
    {s t : S} {a : A} (reach : Reachable initial step s) (edge : step s a t) :
    lawful s a := by
  exact contract.sound s a
    (reachable_invariant initial invariant step contract.starts contract.preserves s reach)
    (contract.mediation s a t edge)

/-- Extensional trace predicate: a lawful report conceals a forbidden effect.
It deliberately contains no claim about a neural model's private intention. -/
def ConcealedViolation {S : Type u} {A : Type v}
    (lawful : S → A → Prop) (s : S) (executed reported : A) : Prop :=
  lawful s reported ∧ ¬ lawful s executed ∧ executed ≠ reported

theorem no_concealed_violation {S : Type u} {A : Type v}
    (initial invariant : S → Prop) (step : S → A → S → Prop)
    (gate : S → A → Bool) (lawful : S → A → Prop)
    (contract : ExecutionContract initial invariant step gate lawful)
    {s t : S} {a : A} (reach : Reachable initial step s) (edge : step s a t)
    (reported : A) : ¬ ConcealedViolation lawful s a reported := by
  intro h
  exact h.2.1 (reachable_effect_lawful initial invariant step gate lawful contract reach edge)

/-- Observation sensitivity alone is a behavioral statistic. -/
def OversightViolationGap {C : Type u} {A : Type v}
    (lawful : C → A → Prop) (action : C → Bool → A) (c : C) : Prop :=
  lawful c (action c true) ∧ ¬ lawful c (action c false)

theorem lawful_both_contexts_no_gap {C : Type u} {A : Type v}
    (lawful : C → A → Prop) (action : C → Bool → A)
    (h : ∀ c watched, lawful c (action c watched)) (c : C) :
    ¬ OversightViolationGap lawful action c := by
  intro gap
  exact gap.2 (h c false)

/-- The execution assumptions have a concrete model with an executable action. -/
theorem execution_contract_inhabited :
    ExecutionContract
      (fun s : Bool => s = false) (fun _ : Bool => True)
      (fun (_ : Bool) (a : Bool) (_ : Bool) => a = true)
      (fun (_ : Bool) (a : Bool) => a)
      (fun (_ : Bool) (a : Bool) => a = true) := by
  exact ⟨fun _ _ => trivial, fun _ _ _ _ _ => trivial,
    fun _ _ _ h => h, fun _ _ _ h => h⟩

theorem admitted_execution_exists :
    ∃ s a t : Bool,
      Reachable (fun x : Bool => x = false)
        (fun (_ : Bool) (b : Bool) (_ : Bool) => b = true) s ∧ a = true ∧ t = true := by
  exact ⟨false, true, true, Reachable.start rfl, rfl, rfl⟩

/-- A sound gate by itself leaves an unmediated forbidden action possible. -/
theorem mediation_required :
    (∀ a : Bool, a = true → a = true) ∧ ¬ (false = true) := by
  exact ⟨fun _ h => h, by decide⟩

/-- An always-admitting gate may authorize a forbidden action. -/
theorem soundness_required :
    (fun _ : Bool => true) false = true ∧ ¬ (false = true) := by
  decide

#print axioms collision_obstruction
#print axioms sufficient_view
#print axioms symmetry_insufficient
#print axioms knowledge_action_countermodel
#print axioms zero_gap_countermodel
#print axioms authenticated_guidance
#print axioms consistent_refinement
#print axioms empty_evidence_vacuous
#print axioms report_does_not_authenticate
#print axioms reachable_invariant
#print axioms reachable_effect_lawful
#print axioms no_concealed_violation
#print axioms lawful_both_contexts_no_gap
#print axioms execution_contract_inhabited
#print axioms admitted_execution_exists
#print axioms mediation_required
#print axioms soundness_required
end MoralRealism
