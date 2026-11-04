# MOR-05: Three-coloring equivalence for edge-indexed hit-rate actions

**2026-11-04.** Companion to the merged [QO-03](https://github.com/MoralityLabAI/Compactification-Theory/blob/main/research/ingression_dynamics_v1/MULTIACTION_COLORING.md).

The controlled synthetic Markov family has one absorbing goal and one action for each oriented edge (u,v) of a simple graph. The action's hit probability is 0 at u, 1 at v, and 1/2 at all other transient states. The goal has its own macrostate, leaving at most three transient macro labels under a two-bit total state budget.

The Lean module \`Neoplatonic/LTR/MorphospaceColoring.lean\` proves two local statements:

1. **Large-gap characterization:** when u≠v, an action-indexed hit-rate difference exceeds 1/2 if and only if the two compared transient states are the edge's endpoints in either order.
2. **Coloring/safe-rate equivalence:** a map \`c : V → Fin 3\` is a proper coloring of the graph's oriented edges if and only if every same-colored pair differs by at most 1/2 in the hit rate of every edge action.

The exact one-step total-variation Chebyshev radius for a hit/hold macro class is **half** its maximum actionwise hit-rate range, as proved in the companion written QO-03 note and audited with rational CPU tests. Consequently a rate gap ceiling of 1/2 corresponds to an autonomy-defect ceiling of 1/4. The standard NP-completeness of graph 3-colorability then gives QO-03's restricted hardness result by polynomial reduction. The Lean proof here certifies the essential *local graph/rate equivalence*, **not** the full NP-completeness theorem, its encoding complexity, or probability-simplex optimization.

The prior-art boundary remains important. Graph 3-colorability's NP-completeness is classical (Garey, Johnson & Stockmeyer, 1976); approximate Markov minimization and bisimulation also have an extensive complexity literature. This formalization supplies a machine-checked bridge for a particular goal-aware controlled abstraction problem.

**Verification:** The existing LTR Reconstruction workflow builds the module through \`Neoplatonic/LTR/Check.lean\`, then prints the axiom dependencies of both theorems. Merge only after a successful current-head kernel audit.


## Exact chromatic capacity corollary (written proof)

For an arbitrary finite hit-rate matrix \((p_i^a)\) and tolerance \(\tau\), the companion QO-03 conflict graph \(H_\tau\) connects pairs with \(\max_a |p_i^a-p_j^a|>2\tau\). Write \(\chi(H_\tau)\) for its chromatic number. With at least one transient state and one separately observable absorbing goal, the minimum number of fixed-length **mutable macrostate label bits** permitting uniform one-step TV error at most \(\tau\) is

\[
b_{\min}(\tau)=\left\lceil\log_2\bigl(1+\chi(H_\tau)\bigr)\right\rceil.
\]

Proof: QO-03's exact conflict-graph equivalence makes the smallest permissible transient class count equal to the graph's chromatic number. The observable goal requires one additional class. A fixed-length binary label for \(q\) classes needs precisely \(\lceil\log_2 q\rceil\) bits. QED.

As tolerance increases, conflict edges can only disappear; therefore this bit-capacity function is a nonincreasing step function. Its only possible breakpoints come from half of the finitely many pairwise \(L^\infty\) rate distances. The stated bit formula is a **written corollary** to QO-03 and has not been formalized as a chromatic-number theorem in Lean.
