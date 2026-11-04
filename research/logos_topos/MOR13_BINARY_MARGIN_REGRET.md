# MOR-13: Exact regret bound from the binary Bellman margin

**November 4, 2026.** Mathematical companion to [QO-15's frozen decision-boundary experiment](https://github.com/MoralityLabAI/Compactification-Theory/pull/55), continuing the QO-14 and MOR-12 work.

Let Q0,Q1 be exact rational horizon-two certificate-reachability probabilities and P0,P1 the corresponding learned estimates. Define the true action margin Δ=Q0−Q1, the predicted margin Δhat=P0−P1, and the predicted greedy action ahat.

[Lean's kernel-checked goal](../../Neoplatonic/LTR/MorphospaceMarginRegret.lean) is the pointwise inequality

\[
 0 \le \max(Q_0,Q_1)-Q_{\hat a}
 \le |\Delta-\widehat\Delta|
 \le |Q_0-P_0|+|Q_1-P_1|.
\]

The companion module proves the upper bound separately when the model chooses cell 0 and cell 1, and proves the elementary triangle inequality that makes the rightmost bound. Summing over any finite evaluation distribution immediately yields a bound on its average regret; unlike MOR-12's \`2 epsilon\` theorem, a supplied *uniform bound* is unnecessary.

For a binary problem, the realized exact-teacher regret simplifies to

\[
\operatorname{regret}
=|\Delta|\,{\bf1}\{\hat a\ne a^\star\}.
\]

That makes the unequal-value states the informative population for decision ranking, while tied states contribute zero regret even when the model's absolute Q-values are inaccurate. A model can therefore reduce mean absolute Q-value error without improving action choices. QO-14's trained 138-parameter RNN displayed precisely this pattern: lower action-value error than the 26-parameter linear model, with both disagreeing with the teacher on 3/8 informative held-out states.

QO-15 fixes independent rate and random-seed families before training. It records the conditional regret on non-tied states, overall regret, margin MAE, Q MAE, and matched full-budget policy outcomes. A positive result must be supported by these recorded held-out observations, not by the Lean theorem alone. The theorem applies to exact mathematical Q-values under the declared planning model and does not prove statistical generalization, teacher calibration, confidence-sequence coverage, or transfer to a larger recurrent model.
