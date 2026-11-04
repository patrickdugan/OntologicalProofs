# MOR-14: Quantitative robustness of a learned binary engagement gate

**November 4, 2026.** This theorem extends MOR-12 and MOR-13 to the post-training engagement selector in [QO-17](https://github.com/MoralityLabAI/Compactification-Theory/pull/61).

For two exact normalized QO-12 progress targets \`q0,q1\`, trained predictions \`p0,p1\`, and fixed gate threshold \`τ=1/20\`, the student chooses a learned probe only when \`max(p0,p1)≥τ\`. Otherwise the public-evidence QO-08 bottleneck policy is the source-fixed fallback.

Assume at an individual queried evidence state that

\[
|p_0-q_0|\le\varepsilon,\qquad |p_1-q_1|\le\varepsilon.
\]

The [Lean theorems](../../Neoplatonic/LTR/MorphospaceGateRobustness.lean) establish

\[
|\max(p_0,p_1)-\max(q_0,q_1)|\le\varepsilon.
\]

Thus either of the following is a sufficient condition for a correct engagement decision:

\[
\max(q_0,q_1)+\varepsilon<\tau
\quad\Longrightarrow\quad
\max(p_0,p_1)<\tau,
\]

\[
\tau+\varepsilon<\max(q_0,q_1)
\quad\Longrightarrow\quad
\tau<\max(p_0,p_1).
\]

The theorem is conditional on per-state error. It proves that gate misclassification requires a teacher score within ε of the fixed threshold, or failure of the stipulated prediction-error bound. QO-17's global or supervised mean absolute error does not provide ε for all visited states. The value of the result is a direct audit target: record empirical teacher-score distances to the gate and model error on frozen policy-visited states, then compare the observed failure rate.

The proof is independent of the model's 26/138-parameter architecture, optimizer, or the Beta predictive interpretation. Anytime certificate coverage continues to depend solely on QO-07's IID/addressability assumptions and the observed evidence.
