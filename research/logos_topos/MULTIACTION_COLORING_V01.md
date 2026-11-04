# MOR-05: Three-coloring equivalence for edge-indexed hit-rate actions

**2026-11-04.** Companion to the merged [QO-03](https://github.com/MoralityLabAI/Compactification-Theory/blob/main/research/ingression_dynamics_v1/MULTIACTION_COLORING.md).

The controlled synthetic Markov family has one absorbing goal and one action for each oriented edge (u,v) of a simple graph. The action's hit probability is 0 at u, 1 at v, and 1/2 at all other transient states. The goal has its own macrostate, leaving at most three transient macro labels under a two-bit total state budget.

The Lean module \`Neoplatonic/LTR/MorphospaceColoring.lean\` proves two local statements:

1. **Large-gap characterization:** when u≠v, an action-indexed hit-rate difference exceeds 1/2 if and only if the two compared transient states are the edge's endpoints in either order.
2. **Coloring/safe-rate equivalence:** a map \`c : V → Fin 3\` is a proper coloring of the graph's oriented edges if and only if every same-colored pair differs by at most 1/2 in the hit rate of every edge action.

The exact one-step total-variation Chebyshev radius for a hit/hold macro class is **half** its maximum actionwise hit-rate range, as proved in the companion written QO-03 note and audited with rational CPU tests. Consequently a rate gap ceiling of 1/2 corresponds to an autonomy-defect ceiling of 1/4. The standard NP-completeness of graph 3-colorability then gives QO-03's restricted hardness result by polynomial reduction. The Lean proof here certifies the essential *local graph/rate equivalence*, **not** the full NP-completeness theorem, its encoding complexity, or probability-simplex optimization.

The prior-art boundary remains important. Graph 3-colorability's NP-completeness is classical (Garey, Johnson & Stockmeyer, 1976); approximate Markov minimization and bisimulation also have an extensive complexity literature. This formalization supplies a machine-checked bridge for a particular goal-aware controlled abstraction problem.

**Verification:** The existing LTR Reconstruction workflow builds the module through \`Neoplatonic/LTR/Check.lean\`, then prints the axiom dependencies of both theorems. Merge only after a successful current-head kernel audit.
