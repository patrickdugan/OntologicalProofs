# From the common divisor to an arithmetic norm

## An unconditional construction

The repository's divisibility grounding model has the unit 1 as its first principle. On the finite set of integers 1,...,N, define the incidence matrix

    Z[d,n] = 1 if d divides n, and 0 otherwise.

For a real coefficient vector v, define its feature at d and its total energy by

    A_N(v)[d] = sum_{n<=N, d|n} v[n],
    E_N(v) = sum_{d<=N} A_N(v)[d]^2 = ||Z v||^2.

The energy is nonnegative by construction. The feature at the unit is the sum of every coefficient, because 1 divides every positive integer. These facts are formalized in `DivisorGram.lean` as `divisor_energy_nonnegative` and `unit_amplitude`, for every finite N and every real vector. No hypothesis about zeta or deity enters either theorem.

The Gram matrix K=Z^T Z has entries

    K[m,n] = number of positive common divisors of m and n.

Every diagonal entry of Z is 1 and Z is upper triangular, so Z is invertible. Its inverse M has entry mu(n/d) when d divides n, and zero otherwise. The finite convolution identity for the Mobius function verifies ZM=MZ=I. It follows algebraically that

    M^T K M = I,     det(K) = 1.

Thus the Gram energy is positive definite, with Mobius inversion providing a change of coordinates. These matrix identities are paper arguments with exact numerical checks; the new Lean module proves nonnegativity, the unit feature, and the two-point example. It does not formalize the general inverse or determinant formulas.

For N=2,

    Z = [[1,1],[0,1]],       K = [[1,1],[1,2]].

The alternating vector (1,-1) has divisor energy 1. Its ordinary squared norm is 2, while the independent reflection form from `ReflectionPositivity.lean` assigns -2. Each form is fully specified, so their differing values give an explicit check against confusing arithmetic positivity with reflection positivity.

## A concrete analytic target already exists

Suzuki's Theorem 1.4 in *On the Hilbert space derived from the Weil distribution* gives an RH-equivalent norm identity for an explicitly defined operator. In his notation,

    || P-hat_{D psi} ||_L2^2 = pi <psi,psi>_W

for every smooth compactly supported psi on the real line, with D psi = i psi'. The operator comes from formulas (1.5)-(1.7), independently of assuming RH; the equality is the RH-equivalent claim. A specified countable choice of tests also suffices. See the original definitions and domains before implementing this operator:

https://www.cambridge.org/core/journals/canadian-journal-of-mathematics/article/on-the-hilbert-space-derived-from-the-weil-distribution/FD33EBD117A6B448053450DD8D62ADB6

This gives a precise residual to study:

    R(psi) = || P-hat_{D psi} ||_L2^2 - pi <psi,psi>_W.

The paper proves that vanishing for the full required test class characterizes RH. The present repository has no implementation or formalization of this analytic operator. Our divisor transform is a separate unconditional construction.

## What would connect the constructions

A productive next mathematical attempt would specify maps from divisor coefficient vectors to the analytic test space, along with normalizations and a controlled limiting procedure. One would then need to show that the resulting Gram form converges to the actual Weil form, or to establish Suzuki's norm identity by another route.

The proof obligations include the contributions from prime powers and the archimedean terms, convergence on the full test class, and control of all terms discarded by a finite cutoff. A positive finite matrix does not supply those estimates. Any subtraction used in a normalization must be audited, because subtracting positive terms can destroy positivity.

For example, a family K_N of positive matrices proves positivity of a target Q only after a justified statement of the form

    Q(f) = lim_N v_N(f)^T K_N v_N(f)

for each required f. Proving existence of v_N alone leaves the displayed equality unresolved. Approximating a selected finite list of tests leaves test coverage unresolved.

## Where the theological premise would enter

A proposed common source of arithmetic explanations could be modeled by a positive state on an algebra of observables, yielding a Gram representation. The additional claim is that this state gives exactly the arithmetic functional in Weil's explicit formula. The existing Scott and grounding premises do not impose that identification, as the combined A6 countermodel shows for the abstract finite setting.

The positive divisor construction supplies a mathematical example of common ancestry and positive geometry coexisting. The norm-matching condition states the extra arithmetic demand. A theorem deriving that demand from a separately defended account of divine intelligibility would constitute new philosophical content; no such derivation has been established here.

## Reproduction

`python3 grammy-and-primes/divisor_gram_experiment.py` checks sizes N=1,...,16 using exact rational matrices. It verifies both Mobius inverse products, the Gram congruence, and determinants, together with 48 exact vector-energy checks. `lake env lean grammy-and-primes/DivisorGram.lean` checks the three stated finite-sum theorems and prints their axiom dependencies.
