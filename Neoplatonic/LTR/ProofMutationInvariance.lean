import Neoplatonic.LTR.NumberedSentenceReindexing

/-!
# Proof mutation invariance: binder names, capture, and specification changes

These are kernel-checked regression witnesses for the distinction between
alpha-renaming and a change in the proposition being proved.

* Benign binder renamings are definitionally equal, even for nested binders.
* The finite-prefix lookup theorem remains valid when proof-local binders
  are renamed.
* Variable capture and quantifier swapping change the assertion. Their
  counterexamples are proved in Lean rather than inferred from a parser error.

No tactic-generated acceptance label or proof text is trusted as an oracle.
The LTR CI compiles this module and audits the named theorems' axioms.
-/

namespace Neoplatonic.LTR

/-- Changing a bound variable name is definitional equality in Lean. -/
theorem proofMutation_forallAlphaEq (P : ℕ → Prop) :
    (∀ x : ℕ, P x) = (∀ renamed : ℕ, P renamed) := by
  rfl

/-- The same property holds when an inner binder depends on an outer one. -/
theorem proofMutation_nestedAlphaEq (R : ℕ → ℕ → Prop) :
    (∀ x : ℕ, ∃ y : ℕ, R x y) =
      (∀ outer : ℕ, ∃ inner : ℕ, R outer inner) := by
  rfl

/-- An independently named proof of the existing explicit prefix bound.
The bound itself is an actual statement about the LTR numbering, rather than
a toy propositional tautology. -/
theorem proofMutation_lookupPrefixRenamed (lookup : ℕ → ℕ) (n : ℕ) :
    ∀ renamed : ℕ, renamed < n →
      lookup renamed < sentenceIndexPrefixModulus lookup n := by
  intro renamed hrenamed
  exact sentenceIndexPrefixModulus_gt lookup hrenamed

/-- Swapping forall/exists is a substantive mutation: the natural numbers
have arbitrarily large successors, and have no greatest finite bound. -/
theorem proofMutation_quantifierSwapRefuted :
    ¬ ((∀ x : ℕ, ∃ y : ℕ, x < y) ↔
        (∃ bound : ℕ, ∀ x : ℕ, x < bound)) := by
  intro h
  have hsuccessor : ∀ x : ℕ, ∃ y : ℕ, x < y := by
    intro x
    exact ⟨x + 1, Nat.lt_succ_self x⟩
  obtain ⟨bound, hbound⟩ := h.mp hsuccessor
  exact (lt_irrefl bound) (hbound bound)

/-- Reusing the name x for an inner binder captures the reference to
the outer x. The captured statement is false, unlike its source. -/
theorem proofMutation_captureRefuted :
    ¬ ((∀ x : ℕ, ∃ y : ℕ, x < y) ↔
        (∀ x : ℕ, ∃ x : ℕ, x < x)) := by
  intro h
  have hsuccessor : ∀ x : ℕ, ∃ y : ℕ, x < y := by
    intro x
    exact ⟨x + 1, Nat.lt_succ_self x⟩
  obtain ⟨witness, hwitness⟩ := h.mp hsuccessor 0
  exact (lt_irrefl witness) hwitness

end Neoplatonic.LTR
