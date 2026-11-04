# MOR-06: A canonical square theorem for two-action rate abstractions

**2026-11-04.** Mathematical companion to [QO-04](https://github.com/MoralityLabAI/Compactification-Theory/pull/41). This Lean contribution certifies the geometric **local equivalence** underlying the finite two-action algorithm and NP-completeness reduction; it does not attempt to formalize the SIAM 1984 complexity-theoretic premise or the polynomial-time reduction itself.

## Theorem

For rational hit-probability vectors \(p=(p_1,p_2)\) and \(q=(q_1,q_2)\), define rate compatibility at box side \(r\) by

\[
|p_1-q_1|\le r,\qquad |p_2-q_2|\le r.
\]

For a finite set of points \(T\), let \(\underline x\) and \(\underline y\) be the **separately attained minimum coordinates**. The main Lean theorem proves

\[
\forall p,q\in T,\ \|p-q\|_\infty\le r
\quad\Longleftrightarrow\quad
\forall p\in T,\quad
(\underline x,\underline y)\le p\le(\underline x+r,\underline y+r)
\]

with all inequalities interpreted coordinatewise. It also certifies each implication separately.

The exact code is in [MorphospaceSquareCover.lean](../../Neoplatonic/LTR/MorphospaceSquareCover.lean). The minimum coordinates are explicit parameters with witnesses in the finite set. Their existence follows from finite nonempty rational order and is not itself reproved by this module. These witnesses may be different points, which is why the geometric search considers at most \(n^2\) *mixed-coordinate* lower corners, rather than simply placing squares at existing input points.

## Relation to complexity results

QO-04's polynomial algorithm for fixed \(d,k\) uses at most \(n^d\) candidate lower corners and chooses at most \(k\) cubes. In two dimensions this is \(O(n^{2k+1})\) rational comparisons. The hardness result for **two actions** involves a variable tolerance and a variable macrostate budget, via Megiddo and Supowit's classical axis-aligned unit-square stabbing problem, and an explicit padding argument for bit-coded class budgets.

Lean MOR-05 separately formalizes QO-03's coloring/rate-gap equivalence for a variable action alphabet. MOR-06 adds the *geometric representation* needed when the action alphabet is held at two.

These statements apply to known finite hit/hold kernels with a separately observable absorbing goal. They say nothing about physical agents, neural consciousness, general Markov-chain compression, or measured AGI performance.

## Acceptance

\`Neoplatonic/LTR/Check.lean\` imports MOR-06 and prints the kernel axiom dependencies of its three new theorems. A successful LTR Reconstruction workflow at the submitted PR head is required before merge.
