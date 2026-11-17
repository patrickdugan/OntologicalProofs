# A common source, a positive norm, and the missing arithmetic identity

Continuation of Grammy and Primes, 2026-10-28. Base commit: `3b7c5a677efde1de1a9333c03eb52e35c0b71396`. The new files are `ReflectionPositivity.lean` and `positivity_experiment.py`. All spectra computed here are synthetic. The analytic connection uses the published Weil criterion; that criterion is not formalized in these new Lean theorems.

## 1. A finite theorem with an explicit falsifier

Let I be a finite set, let tau be an involution on I, and assign each index a strictly positive real weight w_i. Define

    Q_tau(v) = sum_i w_i v_i v_{tau(i)}.

Then

    [Q_tau(v) >= 0 for every real vector v] iff [tau(i) = i for every i].

For the forward direction, suppose tau(a)=b differs from a. Involutivity gives tau(b)=a. Take v_a=1, v_b=-1, and every other coordinate zero. Direct substitution gives

    Q_tau(v) = -w_a-w_b < 0.

For the reverse direction, fixed indices turn Q into sum_i w_i v_i^2, whose summands are nonnegative. The proof tolerates unequal weights on the two-cycle. In a complex Hermitian version the reflection should preserve weights; multiplicities of conjugate-reflected zeta zeros have that property.

`negative_witness` implements the calculation. `positive_iff_fixed` proves the equivalence. If coordinates satisfy x_{tau(i)}=1-x_i, `positive_forces_alignment` gives x_i=1/2. This is finite linear algebra applied to an abstract spectrum.

Index distinct spectral points, using multiplicities as positive weights. Swapping duplicate labels for the same on-axis point would add spurious antisymmetric directions that the actual evaluation space cannot distinguish.

## 2. Test coverage is a mathematical premise

The witness above must be available in the allowed test space. `positive_on_separating_tests_forces_fixed` names this premise explicitly: every moved orbit has its antisymmetric spike among the admissible tests.

There is a sharp counterexample when tests are restricted to reflection-invariant vectors. If v_{tau(i)}=v_i, the form is nonnegative for every such test, even with an off-axis two-cycle. In the unweighted two-point example,

    Q(1,1)=2,        Q(1,-1)=-2.

Both vectors have ordinary squared Euclidean norm 2. `symmetric_tests_miss_negative_mode` formalizes the restricted-test failure. `zero_weights_nonnegative` records a second missing-hypothesis failure: setting both orbit weights to zero erases the witness.

There is also a finite interpolation interpretation. For distinct real coordinates x_1,...,x_N, Lagrange interpolation realizes any prescribed v_i as P(x_i), with degree(P) <= N-1. Consequently, positivity on all such polynomial evaluations has the same force as positivity on all vectors. This paragraph supplies a paper derivation; interpolation is not included in the new Lean file.

For an off-axis pair 1/2 +/- delta, the fixed odd test P(x)=x-1/2 gives Q=-2 delta^2. The normalized separating test P_delta(x)=(x-1/2)/delta gives Q=-2, with coefficients growing as delta tends to zero. `shrinking_odd_test` checks the algebraic defect. This explains why small finite numerical residuals need an error analysis.

## 3. What the arithmetic version would require

For the actual Riemann zeta function, reflection sends rho to 1-conjugate(rho). In Mellin-transform notation, the spectral pairing has the form

    sum_rho F(rho) conjugate(F(1-conjugate(rho))),

with multiplicities and the summation convention and test-function hypotheses required by the explicit formula. Under RH the terms become absolute squares. The converse belongs to Weil's positivity criterion and requires the specified analytic test class. Suzuki's published formulation uses compactly supported smooth functions and the Fourier transform after moving the critical line to the real axis; see equations (1.1)-(1.2) in [S1].

The finite spike proof does not permit prescribing arbitrary values at infinitely many zeta zeros. Polynomial interpolation on finitely many coordinates does not control the remaining zeros, convergence, or membership in the actual test class. These obligations remain visible when passing from the finite model to Weil's theorem.

An actual mathematical route would construct an independently defined linear feature map A, prove its domain and convergence properties, and establish

    Q_Weil(f) = ||A f||^2

for every required test function. The right side is nonnegative, so the published Weil criterion would imply RH. `gram_realization_forces_fixed` checks the finite counterpart using a linear map and an explicit matching identity. The identity is an argument of the theorem. Existence of some Hilbert space or some positive norm supplies no such identity.

## 4. A stronger ontological countermodel

`common_root_scott_a6_with_negative_reflection` constructs one model with all of the following facts simultaneously. It has Scott's full axiom structure on a one-world symmetric frame. A grounding theory supplies its unique first principle. The Scott God-like witness is that same root, and A6 holds: being ungrounded is positive. Ordinary squared norms are nonnegative. The independent two-point reflection form still has value -2 on an explicit vector.

The construction uses `rootScott`, whose positive properties are those held by `false`, and the existing `twoBeingGround`, where `false` grounds `true`. It strengthens the earlier example in which the God-like witness and the first principle were different individuals.

This countermodel refutes the abstract inference from those existing ontological premises to universal reflection positivity. It establishes no independence result for the literal Riemann hypothesis. Its spectrum is freely adjoined finite data.

A theological proposal can now state a precise additional claim: divine grounding yields a canonical arithmetic feature map whose Gram form equals the Weil form on the full test space. A negative Weil witness would refute the conjunction of that proposal and the claimed divine-grounding model. Selecting the arithmetic map, and justifying its matching identity, are the substantive requirements.

## 5. An important qualification about equivalent criteria

The earlier bridge audits prove valid logical equivalences. Those equivalences alone do not establish that a concrete mathematical criterion is circular. Li's criterion and a fully specified spectral realization can be equivalent to RH while supplying different constructions and proof methods. Bombieri and Lagarias explicitly relate Li's coefficients to the Guinand-Weil formula [S2].

The arbitrary-proposition factorization theorem only concerns an unrestricted intermediate proposition. A defined operator with a specified domain carries mathematical obligations that an arbitrary proposition does not express. Likewise, `scott_constant_positivity_iff_truth` shows the consequence of Scott's full premises for constant properties; it does not prove that an independently constructed positive arithmetic form would be empty evidence. This continuation adopts that narrower interpretation of the earlier word 'vacuous'.

## 6. Exact finite experiment

Run `python3 grammy-and-primes/positivity_experiment.py`. It uses Python's standard-library Fraction type throughout, with no floating-point eigenvalue decisions. The local run enumerated all 1,116 labelled involutions on sizes 0 through 8 and applied three positive weight schemes, producing 3,348 weighted cases. Some schemes coincide at small sizes, so these are parameterized cases, not 3,348 distinct quadratic forms.

It checked 17,280 explicit negative witnesses. For all 132 weighted cases through size 5, an independent exact Gaussian-elimination routine computed every principal minor of the symmetric matrix representing Q and confirmed that positive semidefiniteness holds exactly for the identity reflection. All 5,394 tested reflection-invariant vectors passed positivity, including cases whose antisymmetric directions were negative. Invalid involutions and zero weights are rejected by the hypothesis validator; a separate zero-weight control demonstrates why that condition matters.

These numbers describe executed finite tests. They measure no distribution of actual prime pairs or zeta zeros.

## Verification

    lake build Neoplatonic
    lake env lean grammy-and-primes/ReflectionPositivity.lean
    python3 grammy-and-primes/positivity_experiment.py

The Lean file prints the axiom dependencies of all 13 new theorems. The scoped CI compiles every Lean script in this folder and rejects `sorryAx`. Read the current PR run for the exact checked commit. The analytic Weil criterion and the interpolation paragraph remain external mathematical arguments.

## Sources

[S1] Masatoshi Suzuki, On the Hilbert space derived from the Weil distribution, Canadian Journal of Mathematics, published online 2025. Introduction, equations (1.1)-(1.2); https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/on-the-hilbert-space-derived-from-the-weil-distribution/FD33EBD117A6B448053450DD8D62ADB6 .

[S2] Enrico Bombieri and Jeffrey C. Lagarias, Complements to Li's Criterion for the Riemann Hypothesis, Journal of Number Theory 77 (1999), 274-287. Author manuscript, sections 1 and 4; https://websites.umich.edu/~lagarias/doc/bombieri.pdf .

Repository premises and witnesses: `Neoplatonic/GodelScott.lean`, `Neoplatonic/GodelGrounding.lean`, and `Neoplatonic/Core.lean` at the base commit named above. The finite theorem is elementary reflection linear algebra; no mathematical priority claim is made.
