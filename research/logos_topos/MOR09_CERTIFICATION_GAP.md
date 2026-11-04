# MOR-09: Certifying progress under nested uncertainty

**Research date 2026-11-04.** Companion to [Compactification-Theory QO-11](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/expected-gap-controller-qo11-20261104/research/ingression_dynamics_v1) and QO-07's time-uniform Bernoulli evidence ledger.

[Lean theorem module](../../Neoplatonic/LTR/MorphospaceGapMonotonicity.lean) proves eight deterministic statements for rational finite partitions with explicit optimum witnesses:

1. Inward interval refinement can only shrink a robust interval radius and increase a positive certified separation.
2. A pointwise shrinking upper bound has a shrinking minimum; a pointwise rising lower bound has a rising minimum.
3. Optimizing over the *same fixed family* of partitions gives a nonnegative, nonincreasing difference G = min(R) - min(L), given the per-partition lower/upper consistency contract.
4. Feasibility R<=tau or infeasibility L>tau persists under further nonempty nested evidence.
5. For any planning weight 0<=p<=1, the expected one-step gap reduction is nonnegative when both hypothetical next gaps are at most the present gap.

The theorem requires a **nonempty and unchanged partition family** and valid minimum witnesses. The QO-07 implementation constructs those witnesses by finite search; this Lean module formalizes the order-theoretic deductions independently of that Python algorithm.

**Statistical boundary.** This PR makes no claim about the validity of the Beta planning predictive, the beta-binomial e-process, optional stopping, or how quickly the gap shrinks. Those live in QO-07's separate probability argument and QO-11's source-hashed synthetic pilot. An empty confidence interval invalidates this theorem's nonempty-evidence premise. The policy's exact planning costs and fallback rates are measured separately.

Run the existing LTR reconstruction and kernel axiom checks on the final PR head. Neither the theorem nor its accompanying digital experiment establishes biological or phenomenological agency.
