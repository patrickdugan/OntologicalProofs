# Compatible-clean-prefix e-process under adaptive erasure and flipping

Status: conditional mathematical note, independent of any model-training result.

## Precise claim

Let ((X_i)_{i\ge1}) be clean bits on a filtered probability space with filtration ((\mathcal F_i)). Let (E_0=1) and (E_n=\prod_{i=1}^n M_i), where (M_i\ge0), (M_i) is adapted and
\[
\mathbb E[M_i\mid\mathcal F_{i-1}]\le
0.2(0.25)+0.8(1.1875)=1.
\]
This conditional bound is a substantive assumption: it must hold under the specified null for every admissible clean history and every predictable choice of multiplier parameters.

Let (Y_{1:n}) be observations from an adaptive flip/erasure process. Its compatible set (C_n(Y_{1:n})\subseteq\{0,1\}^n) must contain the **actual ordered clean prefix** (X_{1:n}) almost surely. In particular, erasures preserve their original indices and all consistency constraints imposed by the observation process. Compatibility must reflect what the specified corruption channel could produce, rather than an arbitrary imputation or a subsequence with indices compressed.

Define the conservative declaration time
\[
\tau = \inf\{n\ge0 : \inf_{x\in C_n(Y_{1:n})} E_n(x) \ge 100\}.
\]
Here (E_n(x)) is the clean test statistic computed on candidate clean prefix (x), using the *same predictable rules* that define the actual clean statistic.

Since (X_{1:n}\in C_n(Y_{1:n})), pathwise
\[
\inf_{x\in C_n(Y_{1:n})}E_n(x)\le E_n(X_{1:n}).
\]
Consequently
\[
\{\tau<\infty\}\subseteq\{\sup_{n\ge0}E_n(X_{1:n})\ge100\}.
\]
The nonnegative clean e-process is a supermartingale, so Ville's inequality yields
\[
\Pr_0(\tau<\infty)\le 1/100 = 0.01.
\]
No independence assumption about the flip/erasure strategy is needed for this **event-inclusion argument**, provided clean compatibility remains true and the clean conditional e-process inequality remains valid under the underlying null.

## Important boundaries

* The pointwise minimum over compatible histories is **not asserted to be a supermartingale**.
* If flips are permitted without constraints, the compatible set may encompass both bit values at many indices, reducing power substantially. Coverage still holds.
* If the corruption mechanism can exclude the true prefix, the inclusion proof fails. Check compatibility explicitly in tests.
* If the numerical multiplier bound is an unconditional average only, it is insufficient. Check conditional predictability and the full null class.
* Finite-time Monte Carlo can probe implementation and power; it cannot establish the all-time 1% guarantee. The displayed probability bound follows from the assumptions and Ville's inequality.
* Compatibility may grow exponentially. Use an exhaustive finite oracle on short sequences before attempting a dynamic program or approximate minimum. Any approximation used for declarations must be a certified lower bound on the true minimum.

## Falsifiable CPU exercise: ERASURE-E01

Implement an independent tiny finite-horizon oracle and a streaming algorithm with horizon 12. Include adversarial flip/erasure strategies that see prior observations and permitted past clean bits, retain positions, and never remove the true clean sequence from the compatibility set. Compare every streamed minimum with the exhaustive oracle and test all compatible prefixes for small n. Include deliberately broken index-compaction and true-prefix-exclusion implementations as negative controls.

Use a null process whose conditional multiplier distribution satisfies exactly the assumed bound, including edge-case probabilities, and compare clean and conservative crossing events. Record false-crossing frequency with binomial uncertainty across fixed seeds, power loss relative to the clean statistic, compatible-set sizes and runtime. Supply an explicit fixture where an adaptive strategy erases strategically and one where an observed flip is known to be allowed. Pre-register horizon, threshold, seeds, null distribution and strategies before the first randomized run.

**Hard pass gate:** zero event-inclusion violations in exhaustive cases; zero streaming-vs-exhaustive discrepancies; negative controls must trigger detectable faults. Then deliver a reproducible CPU receipt, with source SHA, command, tests, and assumptions. Keep training and GPU spending outside ERASURE-E01. A model-eval use of the result requires a separate mapping from observed model events to clean bits and a justified conditional null.

## Connection to OCA-SW-02

This is a possible tool for *sequential evidence accumulation under observation corruption*. It does not constitute an ontological proof, establish moral realism, or certify a neural model's internal alignment. Use it only if the experiment specifies what clean events are, what is hidden or corrupted, and why the null gives the multiplier bound.

Referenced mathematical result: Ville's maximal inequality for nonnegative supermartingales.
