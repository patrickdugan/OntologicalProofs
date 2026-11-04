# MOR-11: Rational certificate-probability Bellman lemmas

**November 4, 2026.** Mathematical companion to [Compactification-Theory QO-13](https://github.com/MoralityLabAI/Compactification-Theory/pull/52). The Lean source [MorphospaceCertificateReachability.lean](../../Neoplatonic/LTR/MorphospaceCertificateReachability.lean) formalizes:

- A Bernoulli predictive convex combination of two success probabilities in [0,1] remains in [0,1].
- Raising either continuation success probability cannot decrease the predicted success probability.
- A maximum over a fixed finite menu preserves pointwise monotonicity, with explicitly supplied maximizing witnesses.
- Certificate success is absorbing at value 1, and invalid confidence-set branches that have value 0 contribute only the valid branch's probability.
- The exact two-cell Beta arithmetic underlying QO-13's **strict one-query-zero / two-query-19/21** delayed certificate witness.

The zero-to-19/21 claim is an arithmetic theorem tied to the **model-specific** history and its QO-07 likelihood interval calculation, which is independently checked by QO-13's replayed-ledger Python oracle. The Lean module does **not** formalize the full Beta-binomial infinite-time e-process, the exact interval bisection, or a full finite Bellman dynamic program over all histories.

The source is included in the existing LTR Check.lean axiom audit. Merge only after the full current-head Lean kernel workflow passes.

Established context: Howard et al. (2021), https://doi.org/10.1214/20-AOS1991; Cheng & Huan (2026), https://arxiv.org/abs/2509.21734. This is a formalization of finite rational decision inequalities, with no claim of neural or biological agency.
