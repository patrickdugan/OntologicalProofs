# MOR-07: Rational interval geometry for an anytime-valid quotient controller

**2026-11-04.** This is a mathematical companion to [QO-07](https://github.com/MoralityLabAI/Compactification-Theory/blob/main/research/ingression_dynamics_v1/ANYTIME_ACTIVE_QUOTIENT.md), which joins beta-binomial confidence sequences to exact robust goal-preserving hit/hold quotient optimization.

The Lean module [MorphospaceAnytimeIntervals.lean](../../Neoplatonic/LTR/MorphospaceAnytimeIntervals.lean) formalizes a deliberately narrow but crucial deterministic layer:

- Given a rational interval [lo,hi], its midpoint predicts every admissible p with absolute error at most (hi-lo)/2.
- Every competing predictor q suffers absolute error at least that half-width on one endpoint. Together these certify the **exact minimax radius** for the interval.
- Two individually valid confidence intervals may be intersected by taking the maximum lower endpoint and minimum upper endpoint while preserving containment of their common true parameter.
- If a Bernoulli hit rate is wholly unobserved, the uniform worst-case error of any point forecast across [0,1] is at least 1/2.
- A positive separation between a lower bound for one true probability and an upper bound for another is a certified lower bound on their absolute difference.

These are rational inequalities with explicit hypotheses. They support QO-07's finite robust quotient interval arithmetic and its observable decision certificates.

## Statistical theorem boundary

QO-07's probability guarantee depends on a separate, established **mixture e-process plus Ville maximal-inequality** argument. This Lean PR does **not** formalize the beta-binomial martingale, probability measures on infinite streams, optional stopping, or the global min-over-partitions optimization. The corresponding written statement in QO-07 is that each addressed cell has an infinite IID Bernoulli draw stream and the agent chooses the next cell before observing its next draw.

The code's exact Fraction bisection intentionally rounds statistical intervals outward, retaining the mathematical coverage event. Successful rational unit tests certify the implementation on finite cases, while a general statistical guarantee still relies on its probability-model assumptions.

## Audit and non-claims

All new theorems are imported in the repository's existing LTR Check.lean audit and printed with #print axioms. The final-head LTR Reconstruction workflow must pass before integration. The goal is a reusable proof artifact for finite, addressable hit/hold Markov abstractions. Nothing here implies a biological entity, subjective experience, or nonphysical agency.
