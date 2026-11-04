# MOR-04: Minimal future-goal quotient in Lean

**2026-11-04 formalization.** The finite-state mathematical and numerical companion is [QO-01](https://github.com/MoralityLabAI/Compactification-Theory/pull/37), covering an exact (bits, goal error, total-variation defect) frontier. This Lean module formalizes the *exact deterministic* substrate of that result.

The action interface is an alphabet A and maps F_a:S→S. A declared goal readout g:S→Bool induces an observational equivalence:

    s ≈_g t  iff  for all finite action words w,
                   g(F_w(s)) = g(F_w(t)).

The [MorphospaceGoalFuture.lean](../../Neoplatonic/LTR/MorphospaceGoalFuture.lean) module introduces:

- the equivalence relation and its Setoid;
- action congruence and compatibility of the canonical quotient action via Quotient.map;
- well-defined goal readout on equivalence classes via Quotient.lift;
- the **minimality direction**: any exact goal-preserving macro-model identifies only states related by future-goal equivalence;
- a witness theorem converting a distinguishing action word into a proof that any such macro-model must retain two distinct labels.

Together the quotient construction and minimality theorem show that the canonical quotient is the coarsest exact goal-preserving action abstraction. Finite-state cardinality and bit-count formulas have written proofs and exact finite CPU tests in QO-01. This Lean module does not yet formalize a general Fintype.card inequality, the stochastic total-variation minimax program, or the source-hashed CPU receipt.

These are classical Moore/Myhill–Nerode-style constructions. New research lies in applying the exact minimal abstraction as a baseline for jointly optimized **goal retention and approximate predictive autonomy**, followed by frozen out-of-distribution tests.

The standard LTR kernel and axiom-audit workflow imports the new module and prints dependencies of the new theorems. The PR remains draft until the *final head commit* passes that workflow. No statement about consciousness or metaphysical causation is part of the formal theorem.
