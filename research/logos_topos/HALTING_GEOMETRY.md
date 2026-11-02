# LTR-04: A Gödelian obstruction to geometric regularity

## The objective

This note isolates a pure mathematical result: bounded additive observation
delay, equivalently a finite Lipschitz bound in the first-disagreement
geometry, is algorithmically undecidable even for an effectively presented
family of total continuous maps of Cantor space.

The result makes essential use of a theorem of computability theory rather
than treating arithmetic undecidability as an external assumption. Mathlib
contains a universal partial-recursive code evaluator and proves the halting
problem is undecidable for these actual codes.

Lean source: Neoplatonic/LTR/HaltingGeometry.lean.
Supporting modules: Acceleration.lean, DepthProfile.lean, Quantitative.lean.
The kernel workflow is the verification authority. All statements about
effectivity below refer to the specified program-code presentation.

## 1. A uniform family of total Cantor-space maps

Let 2^N denote the set of infinite Boolean streams. Equip it with the
first-disagreement ultrametric

    d(x,y) = 0 if x=y; otherwise 2^(-min{n:x(n)!=y(n)}).

Let e range over actual partial-recursive program codes. Define the
fuel-bounded Boolean predicate

    H_e(n) = true iff mathlib's Code.evaln n e 0 returns some output.

The evaluation at any fixed stage is finite, and mathlib proves Code.evaln
primitive recursive. It is monotone in n, and it eventually returns some
output exactly when the partial computation e.eval 0 terminates.

Define a *total* stream map F_e by

    F_e(x)(n) = x(2n) if H_e(n) is true;
                x(n) otherwise.

Every output coordinate depends on one explicitly computable input
coordinate. Therefore F_e is continuous in the product topology. Moreover
the evaluation (e,n,x) |-> F_e(x)(n) is uniformly computable in e,n and an
oracle for the stream x.

## 2. The logical-delay dichotomy

TranslationDelay(F_e,c) means that agreement through n+c source bits
always implies agreement through n output bits.

**Theorem.** The following are equivalent for each program code e:

    exists c : Nat, TranslationDelay(F_e,c)
    iff e.eval 0 does not halt.

Proof. If e never halts, H_e(n) is always false and F_e is the identity,
which has delay zero.

If e halts, there is a stage n0 beyond which H_e(n) remains true. Given
any proposed delay c, take n >= n0 with n > c+1. Let x be the all-zero
stream and let y differ from x only at coordinate 2n. Then x and y
agree through n+1+c source observations, while F_e(x) and F_e(y)
disagree at output coordinate n. So delay c fails. This works for every c.

Lean proves this reduction with concrete Boolean stream witnesses. It also
proves stage monotonicity and the equivalence between stage activation
and the actual partial-recursive evaluation domain.

## 3. The geometric consequence

The LTR v0.2 theorem, verified independently in Lean, identifies delay c
exactly with

    d(F_e(x),F_e(y)) <= 2^c d(x,y)  for all x,y.

Consequently

    exists c : Nat, F_e is 2^c-Lipschitz
    iff e.eval 0 does not halt.

The program e -> the syntactic description of F_e is effective. Therefore
an algorithm deciding whether F_e admits any finite dyadic Lipschitz
constant would decide the complement of the halting problem. This is
impossible by mathlib's ComputablePred.halting_problem.

A general finite real Lipschitz bound is equivalent to a finite dyadic
bound, since every finite nonnegative real number is dominated by some
power of 2. This Archimedean step is a written argument in this release;
the Lean undecidability statement directly quantifies over dyadic bounds.

## 4. A single observable can witness the obstruction

Let o denote the all-zero stream and set a(z)=d(z,o), a 1-Lipschitz
observable. If e eventually halts, use the pair (o,y_n) where y_n has
exactly one true bit at 2n. For all sufficiently large n:

    d(o,y_n) = 2^(-2n),
    a(F_e(y_n)) - a(F_e(o)) = 2^(-n).

Thus the Lipschitz ratio for the pullback a o F_e is 2^n, and it is
unbounded. In the nonhalting case F_e=id, so the pullback is 1-Lipschitz.

This gives a fixed-observable manifestation of the obstruction. Its
explicit unbounded-ratio proof is recorded here; formalization as a
standalone Lean theorem is a follow-up.

In any spectral realization with commutator seminorm equal to the
Lipschitz seminorm, the question of whether this pullback remains in the
Lipschitz algebra inherits the same halting-hardness. The existence of
such metric-realizing spectral triples for compact metric spaces is
established by Christensen and Ivan (2007). This note does not assert
that the eigenvalues of a canonical Dirac operator encode halting.

## 5. Relation to finitely axiomatized logic

The full Boolean stream is also the completion space of a simple
finitely axiomatized first-order theory: use countably many independent
nullary predicate symbols p_n and one axiom forcing a one-element
domain. Complete theories are determined by the Boolean truth values
of the p_n. Substitution

    p_n |-> p_(2n) if H_e(n);
            p_n   otherwise

extends effectively to all formulas and induces F_e on complete
truth assignments. This is an explicit written realization of the
Cantor-map construction as a syntactic theory endomorphism.

The Lean implementation currently proves the stream theorem using
mathlib's actual partial-recursive program codes. It separately defines
a truth-preserving first-order completion translation interface in
TheoryMaps.lean. A kernel-checked construction of this nullary-predicate
language, its semantic homeomorphism with Cantor space, and the induced
syntactic substitution is a further integration task.

## 6. Limits and novelty

- The halting theorem and all bounded-evaluation principles come from
  established mathlib computability theory.
- The mathematical reduction is explicit and independently checkable.
- The project has not established a novel incompleteness theorem or
  priority over earlier effective topology results.
- The result is a computability obstruction to geometric regularity,
  not an identification of all formal systems with an intrinsic metric.
- Interpretation as divine Logos belongs to the later philosophical
  discussion; no theological terms appear in the formal statement.

### Verification

    lake build Neoplatonic.LTR.Check
    lake env lean Neoplatonic/LTR/Check.lean

The dedicated CI checks every theorem's axiom dependencies for sorryAx and
native reduction axioms. The spectral companion's finite audit lives in
Compactification-Theory PR #32, in test_halting_geometry.py.

References:
- mathlib4, Mathlib/Computability/PartrecCode.lean, especially evaln_mono,
  evaln_sound, evaln_complete, primrec_evaln.
- mathlib4, Mathlib/Computability/Halting.lean, theorem
  ComputablePred.halting_problem.
- Christensen and Ivan, Sums of two-dimensional spectral triples,
  Mathematica Scandinavica 100 (2007), 35-60,
  https://arxiv.org/abs/math/0601024 .
