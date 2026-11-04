# MOR-08: Kernel-checkable rational certificate for active experiment lower bounds

**November 4, 2026.** Companion to [EvalMath QI-03](https://github.com/MoralityLabAI/EvalMath/pull/26), which deduces a fractional hitting-set evidence-budget lower bound for distinguishing a baseline quotient from several competing alternatives. The fractional covering inequality is classical LP duality. Its use with adaptive information constraints is grounded in published bandit lower bounds (Kaufmann–Cappé–Garivier, 2016; Lattimore–Szepesvári, 2020).

For a finite alternative-by-probe coefficient matrix A in rational m × n, let x in the nonnegative rational n-cube be an allocation satisfying

    sum_i A[j,i] * x[i] >= 1 for every alternative j.

Let w[i] be the probe costs and y a nonnegative rational alternative weighting satisfying

    sum_j A[j,i] * y[j] <= w[i] for every cell i.

The [Lean module](../../Neoplatonic/LTR/MorphospaceInformationCover.lean) proves the universal **weak-duality bound**

\[
 \boxed{\sum_j y_j\le\sum_i w_ix_i.}
\]

It also proves that matching primal and dual values certify a globally minimum-cost fractional allocation, compared against *every* other feasible allocation. A third convenience lemma exposes the dual weighting directly as a universal lower-bound certificate.

The proof uses finite sum rearrangement and order-preserving multiplication by nonnegative allocations. It is independent of any stochastic modeling: the KL transport bound in QI-03 must separately justify that expected probe counts satisfy the covering constraints. The present Lean module **does not formalize** a general LP solver, strong duality, martingales, KL divergence, optional stopping, NP-hardness or the rational vertex enumeration algorithm. The EvalMath implementation independently checks primal and dual feasibility and exact rational objective equality on small finite instances.

The existing LTR Check.lean imports this module and prints the dependencies of all three theorems. Merge requires a passing kernel/axiom audit on the current PR head.

This provides a direct reusable mathematical proof obligation for a compact research controller's experiment-selection budget. Neither statistical efficiency of the controller nor the existence of a substrate-independent mind follows from this certificate.
