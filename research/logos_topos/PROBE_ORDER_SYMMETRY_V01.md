# MOR-12: Order symmetry explains a sparse first-action teaching signal

**2026-11-04**, mathematical companion to [QO-14](https://github.com/MoralityLabAI/Compactification-Theory/pull/53). Its source-fixed CPU experiment distills QO-13's exact horizon-two Bellman values into a tiny recurrent reservoir readout. The held-out sample had **0 out of 378** evidence states with unequal first-action values, and its training sample had just **3 out of 864**. QO-14 reports this action-identifiability failure explicitly.

The [Lean module](../../Neoplatonic/LTR/MorphospaceProbeOrder.lean) proves a narrow, classical independence result. With two independent Bernoulli cells A and B of hit probabilities p and q, and a terminal reward that depends only on the outcome of each identified cell, probing A once then B once and probing B once then A once produce exactly the same expected reward. Explicitly,

    E(A,B) = (1-p)(1-q)r00 + (1-p)q r01
             + p(1-q)r10 + pq r11

equals its reordered expression E(B,A). All probabilities, terminal rewards and calculations are rational. The same equality is shown for Boolean certificate-success indicators, with the result that the first-action value difference is exactly zero when the only admissible two-step plans probe each cell once.

This is a **strictly conditional** theorem. Full QO-13 allows repeating one cell, adapting the next probe to the first outcome, and evaluating a separate certificate after the first observation. Those features can break first-action symmetry. The model-specific Lean statement therefore explains a plausible source of QO-14's rare non-tied supervision without claiming that all QO-13 histories have equal first-action Q values.

The source uses standard field algebra without added assumptions about Platonic forms or consciousness. The repository's LTR Check.lean imports and audits all three new theorems, and the final-head kernel workflow must pass before integration.

The next empirical action-learning target should introduce asymmetric decision costs, additional independent actions, or a longer horizon under new frozen rate families so the exact teacher produces a measurable number of genuinely discriminating first-action labels.
