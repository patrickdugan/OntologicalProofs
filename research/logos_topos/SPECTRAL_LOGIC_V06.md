# LTR-06: Spectral logic on first-order completion spaces

## Statement and status

Let T be any first-order theory, X_T its Stone space of genuine mathlib
complete types and U_phi the clopen locus of a sentence phi. Set

    p_phi(x) = 1 if phi belongs to x, and 0 otherwise.

The Lean module Neoplatonic/LTR/LogicalSpectral.lean constructs this
function as an element of the real continuous-function algebra C(X_T,R),
proves it is an idempotent, and establishes the uniform norm gap

    norm(p_phi) = 0 when U_phi is empty,
    norm(p_phi) = 1 when U_phi is nonempty.

It follows that

    T entails phi  iff  norm(p_not_phi) = 0.

In particular, when phi is independent of T, both the truth projector
and the negated-truth projector have norm one. These theorems hold for
arbitrary first-order theories, with the possibility of inconsistent
theories handled by an empty complete-type space.

## Two-point Dirac recognition of logical disagreement

For any two complete theories x,y, any real mass m, and any nonzero real
scale s, take the symmetric Dirac block

    D = [[m,s],[s,-m]]

and represent p_phi diagonally by

    pi(p_phi) = diag(p_phi(x),p_phi(y)).

Then

    [D,pi(p_phi)]
      = [[0, s*(p_phi(y)-p_phi(x))],
         [s*(p_phi(x)-p_phi(y)), 0]].

The theorem logicalDirac_commutator_zero_iff in
Neoplatonic/LTR/LogicalDirac.lean proves

    [D,pi(p_phi)] = 0
      iff (phi belongs to x iff phi belongs to y).

Its exact mass-independence follows from SpectralBridge.lean. The
commutator detects a distinction labelled by a sentence, rather than
reconstructing the identity of either complete theory by itself.

## Effective norm-zero obstruction

For a code function n -> phi_n, EffectiveSpectral.lean proves

    ComputablePred(n -> norm(p_not_phi_n) = 0)
      iff
    ComputablePred(n -> T entails phi_n).

An undecidable theoremhood predicate therefore gives an undecidable
norm-zero predicate for the explicitly named projections. The theorem
states the undecidability premise separately. For consistent c.e.
extensions of Robinson arithmetic Q, classical essential
undecidability can supply it, but this Lean module does not contain
Gödel/Rosser diagonalization.

The norm has only the values 0 or 1; a uniformly computable rational
approximation to error strictly less than 1/2 would decide norm zero.
That approximation implication is written mathematics in this release.

## Atomic spectral grades for the one-axiom model

The concrete one-axiom nullary theory in Nullary.lean has the actual
complete-type Stone space homeomorphic to Cantor streams. Using the
first-disagreement metric d(x,y)=2^(-first disagreement), the nth atomic
truth function satisfies

    abs(P_n(x)-P_n(y)) <= 2^n * d(x,y).

The bound is attained by the all-false stream and the stream with its
only true bit at coordinate n. Therefore

    Lip(P_n) = 2^n.

AtomicSeminorm.lean proves the Boolean-stream bound and sharp witness.
AtomicTheorySeminorm.lean transfers them to actual complete types.
All three sharpness and transfer theorems passed the Lean kernel audit in
GitHub Actions run 41571751459.

For an infinite Dirac representation with commutator seminorm equal
to the Lipschitz seminorm, the atomic grading becomes

    norm([D,pi(P_n)]) = 2^n.

The analytic infinite direct-sum argument appears in
FILTERED_SPECTRAL.md, and operator-domain formalization remains open.

## Reproducible finite checks

The companion Compactification-Theory PR #32 contains
research/logos_topos_spectral/nullary_projections.py and a new test
module. It exhausts 256 Boolean truth tables over eight possible
completions and every pair of those completions for the Dirac
logical-disagreement test. For a five-bit model it checks that the
atomic Lipschitz quotient agrees with the norm of finite direct-sum
Dirac commutators, independently of the diagonal mass.

The complete companion suite passed 30 tests in run 41571682988.

## Functoriality and conservative network gluing

LogicalPullback.lean proves an actual commuting square for the
one-axiom language's syntactic endomorphisms:

    pullback_F_e (p_phi) = p_(translation_e(phi))

as an equality in the real continuous-function algebra. The
statement is checked for every first-order sentence, including
quantified ones, in run 41572084546.

For any compact spaces X,Y and a continuous surjection f:X->Y,
uniform norm of continuous observables obeys

    norm(a composed with f) = norm(a).

ConservativeSpectral.lean proves this norm-preserving property and
specializes it to truth projections of genuine first-order theories.
The finite-extension hypothesis in Network.lean supplies surjectivity
for certain compatible global diagrams; those network instances must
also show continuous projection and compact global realization.
Both the general continuous-surjection norm theorem and its logical
projection specialization passed the Lean kernel audit in run
41572259359. NetworkSpectral.lean additionally constructs the compact
compatible-state subspace explicitly and proves that finite-extension
compatibility gives an isometric observable pullback. Its proof passed
run 41572903341.

The norm result needs surjectivity. An injective or nonsurjective
map may discard entire truth regions and change the norm of a
projection. Quantitative Lipschitz or Dirac bounds need additional
filtration-delay hypotheses, already isolated in LTR-03.

## Complex C*-projections and conservative spectral gluing

ComplexLogicalSpectral.lean now constructs the genuine complex-valued
function p_phi in the commutative C*-algebra C(X_T,C) on the actual
Stone completion space of any first-order theory. Its checked results
include

    p_phi * p_phi = p_phi
    star(p_phi) = p_phi
    norm_C(p_phi) = norm_R(p_phi)
    T entails phi  iff  norm_C(p_not_phi) = 0.

These passed the Lean kernel and axiom-dependency audit in run
41572990397. They put the earlier real characteristic functions in
the conventional complex C*-algebra setting.

ComplexConservativeSpectral.lean additionally builds on the
network theorem to formulate an exact complex norm-preservation
claim for compatible global state spaces:

    norm_C(p_phi composed with pi) = norm_C(p_phi),

where pi is the surjective continuous projection provided by
finite-extension compatibility. Check its separate CI run before
treating this additional last theorem as kernel-checked.

## Established precedents and research frontier

Christensen and Ivan, Sums of two-dimensional spectral triples,
Mathematica Scandinavica 100 (2007), 35-60, show that compact metric
spaces admit metric-recovering countable two-point spectral triples.
Their earlier Spectral triples for AF C*-algebras and metrics on the
Cantor set, Journal of Operator Theory 56 (2006), 17-46, develops
Dirac operators tied to filtrations of finite-dimensional algebras.
Pearson and Bellissard (2009) give a rooted-tree ultrametric approach.

Burton, Eagle, Fox, Goldbring, Harrison-Trainor, McNicholl, Melnikov
and Thewmorakot, Computable Gelfand Duality (2024), establish a
computable version of Gelfand duality for computably compact metrizable
spaces and computable presentations of unital commutative complex
C*-algebras (arXiv:2402.16672). This directly constrains originality
claims about reconstructing algebraic structure from effective topology.
Alec Fox, Effective metric structure theory of C*-algebras (2023),
provides related work on recursive C*-presentations and real
continuous-function algebras.

These precedents already settle the abstract metric-recovery route.
The distinctive LTR research question concerns the effective names
for first-order sentences and how logical computability, interpretation
maps, and network compatibility survive the spectral representation.

Formal obligations:

1. Define and kernel-check the unbounded infinite direct-sum operator,
   its dense domain, self-adjointness and compact resolvent.
2. Prove that its commutator seminorm recovers the Lipschitz seminorm
   for all admitted observables and its Connes distance recovers d.
3. Connect exact spectral pullback bounds to concrete interpretation
   diagrams, including conservative global gluing.
4. Study effective invariants under bounded-delay changes of sentence
   filtration, checking originality against existing literature.

The mathematics is formulated without theological premises.
