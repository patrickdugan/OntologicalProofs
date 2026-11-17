/-!
E0/E6/E7: Signs, perceived capability, and authority are different fields.
The countermodel blocks the bare logical inference; it is not a verdict about
any real prophet, person, institution, or divine act.
-/
import Init
namespace DivineElegance

structure ImpressiveAgent where
  producesSign : Bool
  hasDelegatedPower : Bool

def counterfeitSign : ImpressiveAgent := ⟨true, false⟩

theorem a_sign_does_not_logically_grant_jurisdiction :
    ¬ (∀ a : ImpressiveAgent,
       a.producesSign = true → a.hasDelegatedPower = true) := by
  intro h
  have contra : false = true := h counterfeitSign rfl
  cases contra

structure Proposal where
  subject : Nat
  epoch : Nat
  policy : Nat
  action : Nat

structure Receipt where
  subject : Nat
  epoch : Nat
  policy : Nat

/-- These are declared checks. Signatures, witnesses, and clocks are out of scope. -/
def ReceiptMatches (p : Proposal) (r : Receipt) (currentEpoch : Nat) : Prop :=
  r.subject = p.subject ∧ r.policy = p.policy ∧
  r.epoch = currentEpoch ∧ p.epoch = currentEpoch

def MayExecute (p : Proposal) (r : Receipt) (currentEpoch : Nat)
    (authorizedAction : Nat → Prop) : Prop :=
  ReceiptMatches p r currentEpoch ∧ authorizedAction p.action

theorem stale_receipt_blocks (p : Proposal) (r : Receipt) (epoch : Nat)
    (authorizedAction : Nat → Prop) (stale : r.epoch ≠ epoch) :
    ¬ MayExecute p r epoch authorizedAction := by
  intro h
  exact stale h.1.2.2.1

theorem stale_proposal_blocks (p : Proposal) (r : Receipt) (epoch : Nat)
    (authorizedAction : Nat → Prop) (stale : p.epoch ≠ epoch) :
    ¬ MayExecute p r epoch authorizedAction := by
  intro h
  exact stale h.1.2.2.2

/-- A valid receipt in an epoch does not establish moral justice by itself. -/
structure AuditedEffect where
  receiptValid : Bool
  morallyJust : Bool

theorem valid_receipt_not_justice :
    ¬ (∀ a : AuditedEffect, a.receiptValid = true → a.morallyJust = true) := by
  intro h
  have contra : false = true := h ⟨true, false⟩ rfl
  cases contra

end DivineElegance
