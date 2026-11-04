# MOR-03: Goal readout and recovery-preserving controlled quotients

**2026-11-04.** This follow-up closes a loophole in pure autonomy-defect minimization: constant macrostate maps can achieve perfect dynamical closure while retaining no useful goal information.

The [Lean module](../../Neoplatonic/LTR/MorphospaceGoal.lean) formalizes:
- an exact Boolean goal readout exists on a surjective quotient iff it is constant on each microstate fibre;
- exact action-by-action semiconjugacy preserves the existence of a goal-reaching prefix of any finite action sequence;
- the same prefix-hitting event is preserved for an explicit micro-goal predicate that factors through the quotient.

The Boolean type represents a chosen operational target, not consciousness, theological purpose or moral agency.

## Mathematical companion

See [IDQ-03](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/goal-visible-quotients-20261104/research/ingression_dynamics_v1/GOAL_RECOVERY.md) for the sharp 0 versus 1/2 minimax goal-readout error, task-signature memory lower bound and an exact finite Markov hitting-probability example with a stochastic TV coupling bound.

**Scope and limitations:** The Lean theorem is pathwise and deterministic under a common action schedule, including any damage/intervention actions covered by the commutation hypothesis. The Markov coupling inequality has a written proof and finite rational tests in Compactification-Theory and is **not** Lean-formalized here.

**Acceptance:** \`Neoplatonic/LTR/Check.lean\` imports this module and prints its kernel axiom dependencies. A passing LTR Reconstruction workflow at the PR's final head commit is required before merging.
