# MOR-01: Morphospace semiconjugacy and formal limits

**2026-11-04 draft.** Source inspiration: Michael Levin's 2026 interviews and [Ingressing Minds](https://doi.org/10.3390/philosophies11050161), especially their description of an embryo as a coordinated goal-directed collective. The results below are ordinary mathematics of controlled dynamics. They are not a theorem establishing Platonic causation, a proof of the existence of a soul, or evidence that a neural system is sentient.

## Context within Logos–Topos Reconstruction

The existing LTR program reconstructs logical observables on marked Stone spaces, with detailed spectral and metric results in [INFINITE_DIRAC_V34.md](INFINITE_DIRAC_V34.md) and the LTR [README](README.md). Those results preserve *sentence and filtration markings*. Their equality or metric claims depend on specified maps.

A different form of structure preservation arises for dynamical systems. Let S and Z be state sets, A an action alphabet, F_a:S→S and G_a:Z→Z. A map p:S→Z is an **action-preserving semiconjugacy** when

    p ∘ F_a = G_a ∘ p     for every a ∈ A.                     (1)

If p is bijective then each F_a and G_a are set-theoretically conjugate, but topological conjugacy further requires appropriate topologies and p a homeomorphism. If p is surjective and noninjective, (1) identifies a quotient of microstates sharing a macro state.

## Theorem MOR-01/T1: path and goal transport

For any finite action word w=(a_1,...,a_n), define F_w by applying actions in order. From (1),

    p(F_w(s)) = G_w(p(s))                                         (2)

for all s and w.

**Proof.** The empty action word is identity. Assuming the claim for the first n actions, apply (1) at the next step and use induction. QED.

For a declared macro-target B⊆Z, (2) implies

    F_w(s) ∈ p^{-1}(B)   iff   G_w(p(s)) ∈ B.                      (3)

Every prefix also satisfies (3), so first-hit indices agree for the same action schedule. A feedback policy observing only projected macro histories picks the same actions on both systems, proving the analogous policy-controlled statement by induction.

The exact theorem for action-list transport and endpoint predicates is written in [MorphospaceSemiconjugacy.lean](../../Neoplatonic/LTR/MorphospaceSemiconjugacy.lean). **Lean build status: UNVERIFIED locally** because elan/Mathlib were unavailable to the authoring runtime. This PR now imports the module from `Neoplatonic/LTR/Check.lean` and prints both theorem axiom dependencies. Promotion to a checked theorem depends on a green LTR Reconstruction workflow at the new head commit.

## Obstruction: a macro partition may fail to be dynamical

Let S={s0,s1,s2}, Z={z0,z1}, p(s0)=p(s1)=z0 and p(s2)=z1. For one action set F(s0)=s2, F(s1)=s1. A candidate G would require G(z0)=z1 and G(z0)=z0 simultaneously. Therefore, a descriptive similarity class cannot automatically be promoted to a dynamical quotient.

This is why **goal resemblance**, even under many observed histories, is weaker than the universal premise in (1). In finite partially observed cases, the appropriate exact equivalence can be constructed by future-action observational partition refinement, as in [XenobotBench MOP-01](https://github.com/patrickdugan/XenobotBench/tree/research/morphospace-quotient-20261104/docs/MORPHOSPACE_QUOTIENT.md).

## Spectral and geometric caveats

A dynamical semiconjugacy says nothing by itself about Connes distances, Dirac commutators, marked Stone clopens, topological continuity or the actual type of a biological organism. A spectral counterpart needs extra hypotheses such as an isometric or controlled-distortion map on the chosen metric presentations and an intertwining or bounded relation between the operators. The existing LTR metric obstruction is relevant: a change of filtration can change the spectral presentation, even when underlying Boolean truth assignments agree.

**Open theorem obligation:** find an experimentally meaningful class of action-preserving maps with both a controlled macro-dynamics error and a certified spectral distortion bound. For stochastic kernels, the finite-horizon coupling bound is developed separately in [IDQ-01](https://github.com/MoralityLabAI/Compactification-Theory/tree/research/ingression-quotients-20261104/research/ingression_dynamics_v1/THEORY.md).

## Exact falsifiers and Lean integration

1. Exhibit microstates in the same proposed macro fibre with different projected successors: rejects (1) immediately.
2. Exhibit an action sequence that changes goal reachability despite equal start macrostate: rejects a claimed exact behavioral transfer.
3. A failure to preserve a chosen Connes distance refutes a proposed *isometric spectral transfer*, while leaving the underlying dynamical statement intact.

Run \`lake env lean Neoplatonic/LTR/MorphospaceSemiconjugacy.lean\`. Once compiled, add an explicit import and axiom check to \`Neoplatonic/LTR/Check.lean\` in a separate integration commit. The present PR leaves existing certified LTR theorem lists untouched.
