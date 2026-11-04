# MOR-12: Certified action regret for an approximate Bellman student

**November 4, 2026.** Formal companion to [Compactification-Theory QO-14](https://github.com/MoralityLabAI/Compactification-Theory/pull/54), which trains a tiny recurrent student on exact certificate-reachability action values.

Let Q(a) be the true QO-13 horizon-two probability of attaining a valid QO-07 certificate after choosing first action a, under the stated Beta planning model. Let Qhat(a) be a learned student's predicted action value. Suppose every action has a certified **uniform** error at most ε:

\[
\forall a,\quad |\widehat Q(a)-Q(a)|\le\varepsilon.
\]

If a* maximizes the exact Q and ahat maximizes Qhat, [the Lean theorem](../../Neoplatonic/LTR/MorphospaceBellmanDistillation.lean) proves

\[
 0\le Q(a^*)-Q(\widehat a)\le2\varepsilon.
\]

The proof compares exact and approximate values at the true-optimal and predicted-optimal actions using the triangle inequality and the ordering of their maxima. The same bound is separately specialized to the two-action case. If the true gap between the preferred and another action exceeds 2ε, the approximate predictor preserves the true action order. An exactly matching student has zero action regret.

These are standard approximate dynamic-programming inequalities, formalized here for the QO-13/QO-14 mathematical interface. The theorems apply **conditionally** on a supplied uniform-error premise. QO-14's supervised test error is an empirical aggregate and does not by itself establish that every unseen evidence state satisfies a uniform ε bound.

The Lean proof audits four theorem axiom dependencies through the existing LTR Reconstruction workflow. It does **not** certify training, hidden-state identification, model generalization, Bayesian predictive calibration or the separate QO-07 anytime confidence-sequence theorem. QO-14's trained eight-unit recurrent controller, linear baseline and held-out policy experiment remain empirical work.
