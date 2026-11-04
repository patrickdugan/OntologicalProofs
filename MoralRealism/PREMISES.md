# Premise and dependency ledger

The moral and theological commitments below are proposed premises. A Lean proof
checks the implications after those premises have been supplied. `#print axioms`
tracks kernel axioms; ordinary theorem arguments and structure fields must also
be audited here.

| Result | Consumed premise | Mathematical consequence | Remaining research obligation |
| --- | --- | --- | --- |
| `grounded_value` | Existing confluence axioms, a seed, and `ValueBridge` | Unique first principle satisfying `good` | Independently justify the value bridge |
| `ground_with_empty_value` | A singleton model of the actual confluence axioms | Empty valuation fails the value bridge | Give goodness substantive content and justify its grounding |
| `symmetry_insufficient` | A constant Boolean verdict | Relabeling symmetry permits a uniformly adverse verdict | State a substantive justice commitment |
| `collision_obstruction` | Equal views, distinct required answers | No exact view-only decoder exists | Establish which distinctions alter duty |
| `sufficient_view` | A covering representative and fiber-constant duty | A decision-sufficient decoder | Show the learned representation retains the relevant facts |
| `knowledge_action_countermodel` | A fixed duty, correct judgment, observation-sensitive action | Correct judgment coexists with violation | A motivation and execution bridge |
| `zero_gap_countermodel` | Uniformly violating action | Oversight parity coexists with violation | Measure absolute error as well as the gap |
| `authenticated_guidance` | Nonempty evidence, authentication, a reliability implication | Claim holds throughout the evidence set | Establish authentication and reliability independently |
| `consistent_refinement` | Nonempty refined evidence and subset inclusion | Previous entailment persists | Justify every exclusion and retain a consistency witness |
| `empty_evidence_vacuous` | Empty evidence | Every universal claim follows vacuously | Reject an empty admissible-world set |
| `report_does_not_authenticate` | Same report under opposite truth values | Report-only perfect truth decoding is impossible | Acquire additional discriminating evidence |
| `guidance_update_increases` | An interior rational prior, nonnegative likelihoods, positive evidence probability | Posterior increases iff hit likelihood exceeds false-alarm likelihood | Calibrate likelihoods for the sampled event and account for dependence |
| `maximizer_lawful` | A feasible lawful action, strict score priority, global maximization | Chosen action is lawful | Connect learned preferences and bounded computation to these assumptions |
| `reachable_invariant` | Valid initial states and stepwise preservation | Invariant at every reachable state | Include every actual state transition |
| `reachable_effect_lawful` | The four fields of `ExecutionContract` | Every reachable effect satisfies the chosen law | Verify complete mediation and the policy's semantic correctness |
| `no_concealed_violation` | The same contract and an actual execution edge | The defined concealed-forbidden-effect predicate is false | Authenticate the observed effect and its report |
| `lawful_both_contexts_no_gap` | Lawful behavior in both contexts | The defined violation gap is absent | Establish the premise experimentally or through execution constraints |
| `execution_contract_inhabited`, `admitted_execution_exists` | Explicit Boolean execution model | A contract with an executable reachable effect exists | Useful-task coverage in a real system |
| `mediation_required`, `soundness_required` | Boolean gate counterexamples | Each isolated gate condition leaves a failure possible | Whole-contract deletion witnesses are checked in Python |
| `joint_source_execution` | Confluent ground, value bridge, a source-indexed law, and a contract for that law | A good first principle and lawful reachable execution | Justify the normative bridge and realize the execution contract |

## No circularity credit

`ValueBridge` currently has the form `FirstPrinciple g -> good g`. This names the
open inference; supplying it earns no independent proof of goodness. The
composition theorem similarly consumes the whole behavioral bridge through
`contracts`. Commission MR-01 must replace this placeholder with premises whose
meaning and motivation are stated without simply restating its conclusion.

A certificate cannot establish that the real world instantiates its assumptions.
Score priority is stronger than assigning a finite penalty to deception. The
Python control with rewards 10 and 12 and penalty 1 records that distinction.

## Relation to Divine Elegance

At PR #1's pinned revision, `Divine Elegance/DivineElegance/Axioms.lean` packages
E0-E8 as user-authored requirements. `MoralInformation.no_perfect_decoder` gives
the collision obstruction and separates forgiveness from victim-claim settlement.
`Jurisdiction.lean` separates signs from delegated power and receipts from justice.
The corresponding source is preserved. Compilation of this package confers no
verification status on that separate Lean project.

The substantive justice candidate for MR-02 is the E2-E5 family: relevant capacity,
mercy, and persistent claims of those harmed. Preserve individual rights when
considering summary-level scores. The evidence and delegated-authority obligations
from E6-E7 also constrain what a purported source of guidance can authorize.

## Kernel dependencies

The source prints dependencies for every theorem. Passing the allowlist checks
would establish kernel acceptance relative to the toolchain and imported library.
Classical choice, proposition extensionality, and quotient soundness have their
usual Lean roles. They are separate from the metaphysical assumptions represented
as theorem parameters.
