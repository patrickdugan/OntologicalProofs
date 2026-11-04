# MOR-02: Quotient existence, lower obstruction and compositional defect

**November 4, 2026, mathematical follow-up to [MOR-01](MORPHOSPACE_SEMICONJUGACY.md).**

The pure mathematical results in [Neoplatonic/LTR/MorphospaceMinimax.lean](../../Neoplatonic/LTR/MorphospaceMinimax.lean) are:

1. A surjective deterministic quotient exists **iff** the proposed projection has fibre-consistent successors for every action. The induced macro law is unique.
2. If two microstates in one fibre produce macro successors at distance D, any proposed macro law has one-step error at least D/2 on one of them (triangle inequality).
3. If one approximate quotient has uniform error eps1, a second has error eps2, and the second projection is L-Lipschitz, their composition has uniform error at most L*eps1+eps2.

The exact **minimax identity** lives in [Compactification-Theory IDQ-02](https://github.com/MoralityLabAI/Compactification-Theory/blob/research/ingression-quotients-20261104/research/ingression_dynamics_v1/MINIMAX_THEOREMS.md), including the distinction between an abstract metric centre constrained to an existing finite macrostate set and a freely chosen centre in an ambient normed space. The lean module here formalizes its essential obstruction and exact-zero case; full finite Chebyshev-center optimality is an additional proof obligation.

## What the result does (and does not) establish

A functional macrostate is **dynamically exact** when all states represented by that macrostate have compatible successors under every specified intervention. The formal result establishes a purely operational property about labelled state machines, without assumptions about consciousness, theology, or physical reality.

A counterexample with incompatible successors disproves that specific quotient. The choice of abstraction and its permitted interventions remains part of the mathematical input. For stochastic chains and reversible spectral operators, see [RSITopology QD-02](https://github.com/MoralityLabAI/RSITopology/blob/research/morphospace-dirichlet-20261104/research/morphospace_dirichlet/MARKOV_COMPRESSION.md). Those are written proofs and exact rational witnesses, **not yet Lean-checked operators**.

## Verification

The PR includes an import of this module in the existing \`Neoplatonic/LTR/Check.lean\` and prints the axiom dependencies of all four new theorems. The required acceptance gate is a *successful LTR Reconstruction workflow on the current PR head*, plus the ordinary repository kernel/axiom requirements. Earlier success at a different commit is not sufficient.

    lake env lean Neoplatonic/LTR/Check.lean

Source inspiration: Michael Levin's 2026 interviews on morphospace and basal cognition, interpreted as questions about intervention-compatible organizations. The formalisms here are mathematical deductions from declared state-space assumptions, not statements or results attributed to Levin.
