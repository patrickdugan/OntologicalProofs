# LTR-UG-02: q=2 recurrence certificates

2026-11-04. `Neoplatonic/LTR/UniqueGamesRecursive.lean` defines the rational rank recurrences and proves eight named theorems, with explicit axiom reports in that module. It is imported through `UniqueGamesFinite.lean`, which is already in `Check.lean`'s build closure. Kernel status must be read from the corresponding GitHub Actions run; this note does not predeclare a successful run.

For the recurrences with initial values 1/2, 3/4 and 7/8, the closed forms are

    d1(t) = (1/2)(6/7)^t
    d2(t) = (3/4)(6/7)^t
    d3(t) = (9/10)(6/7)^t - (1/40)(1/7)^t.

The nonlinear sequence is p(t)=(7/8)(6/7)^t. Lean proves

    d3(t)-p(t) = (1/40)((6/7)^t-(1/7)^t)
    d3(t) < (36/35)p(t)
    d3(1)-3/4 = 1/56
    d3(9) < 1/4.

A further theorem formalizes the final scalar implication in the harmonic survival argument: positive H, H*(1-survival)<=drop<=H/2, and detection>=survival/2 imply detection>=1/4. Its stochastic hypotheses remain explicit.

## Scope

The connection between these recurrences and every linear lift of the fixed q=2 recursive gadget is a written proof in Compactification-Theory, backed by an exact finite oracle. The source checks all 16 character subspaces and 1017 local extension maps against 7119 direct restrictions. The oracle also tests the recurrence through depth 64. The complete recursive geometry and optimality argument have not been encoded as Lean structures and theorems here. No claim about the full arbitrary-alphabet UGC reduction follows from this module.

## Reproduction

    lake build Neoplatonic.LTR.Check
    lake env lean Neoplatonic/LTR/UniqueGamesRecursive.lean

The second command prints the dependencies of all eight new theorems directly. Companion proof and executable tests:
https://github.com/MoralityLabAI/Compactification-Theory/blob/20586b081ebc2a3b6ab8b79fc266df5de6fa9fd1/research/levin_sieve_v1/UNIQUE_GAMES_RECURSIVE_V02.md
