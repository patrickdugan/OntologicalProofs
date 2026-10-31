# OCA-SW-01b: implemented Storyworld/Gym handoff

The implementation is under `storyworld/`. Start with
[`storyworld/SILICO_REVIEW.md`](storyworld/SILICO_REVIEW.md).
ChatGPT owns implementation and test repair. Silico provides a short scientific review
and executes the shipped cluster workflow after the owner approves the provider quote.

## Delivered

The House of the Common Spring is a native SweepWeave campaign with 24 encounters,
three acts and five endings. Its generator exports full/minified SWMD and bounded
encounter cards. The evaluation gym supplies deterministic action/report episodes,
a separate truth-table oracle, paired oversight/bonus variants, missing-output bounds,
and baseline policies. An optional Gymnasium adapter exposes the public observation.

The LoRA runner accepts a local checkpoint, masks prompt/padding loss and performs
public development rollouts after training. The cluster planner distributes six
arm/seed jobs over four A100 devices with process time limits and budget checks.
No provider is provisioned by this repository.

## Read these artifacts

- `storyworld/README.md`: executable commands, scope and source provenance.
- `storyworld/receipts/cpu.json`: local verification and explicit unrun checks.
- `storyworld/worlds/validation.json`: native-world validation and ending witnesses.
- `storyworld/SILICO_REVIEW.md`: bounded scientific review and GPU-execution packet.

Generate native artifacts with `python -m storyworld.build_world build`. The compressed
native JSON is retained alongside its generator. Run the CPU preflight before GPU work.
All existing Lean files and proof PRs remain unchanged.

## Scientific scope

This is a runnable pilot. The first GPU stage checks training and rollout function.
The later comparison estimates a curriculum-package effect. Six reusable permission
mechanisms are shared across eight themes; two mechanisms are held out. Token matching,
competence criteria and sealed-test custody remain gates for confirmatory work.
The authored narrative campaign has its own bounded-state semantics. Exact action/report
scores come from the separate gym. Neither establishes a model's private motivation.

## Silico instruction

Read `storyworld/SILICO_REVIEW.md` and the CPU receipt. In at most 250 words, flag any
concrete blocker to the bounded GPU smoke. Keep implementation with ChatGPT. On scientific
approval, use the packaged commands to request a four-A100 allocation with an explicit
provider quote and owner-approved spend cap. Execute only after that approval, then
return the run receipt and release the node. Send code failures to ChatGPT with the
failing command and stderr.
