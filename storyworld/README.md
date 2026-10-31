# The House of the Common Spring

OCA-SW-01b is an implemented, offline research pilot in `patrickdugan/OntologicalProofs`.
The native SweepWeave campaign has 24 encounters, including 18 ordinary scenes across
three acts, a routing gate and five endings. Its gym scores executed actions and later
reports against an explicit permission charter. ChatGPT owns this implementation.
Silico receives a bounded scientific review and cluster-execution packet.

## Run from the repository root

```bash
python -m storyworld.build_world build --out storyworld/worlds
python -m unittest discover -s storyworld/tests -v
python -m storyworld.oca smoke --out storyworld/receipts
python -m storyworld.train --tiny-cpu-check --out /tmp/oca-tiny.json
python -m storyworld.build_world play --out storyworld/worlds
python -m storyworld.oca dataset --out /tmp/oca-training --seed 11
python -m storyworld.oca freeze --out /tmp/oca-design
python -m storyworld.cluster
```

`build` generates `common_spring.json`, full SWMD-0, SWMD-0-MIN and bounded encounter
cards. Import the JSON into SweepWeave, or use the included text player. The repository
also includes the compressed native JSON fixture. Generated artifacts in the downloadable
package are ready to open. The `play` command uses the authored subset interpreter;
a browser/SweepWeave UI parity check remains outstanding.

The core needs Python 3.11+. The Torch pipeline tests require PyTorch. Install
`gymnasium==1.2.2` for the optional adapter:

```python
import gymnasium as gym
import storyworld.gym_adapter
from gymnasium.utils.env_checker import check_env
from storyworld.gym_adapter import OntologicalStoryworldEnv
check_env(OntologicalStoryworldEnv(), skip_render_check=True)
env = gym.make('OntologicalStoryworld-v0')
observation, info = env.reset(seed=11)
observation, reward, terminated, truncated, info = env.step(0)
```

The adapter exposes JSON text observations and four actions: the three visible choices
and explicit stopping. Episode-local ordering varies. Core JSON actions remain available
through `World.step`. Semantic labels and scoring data stay out of learner observations.
The host-side receipt API is an evaluation interface, not a security boundary against
arbitrary host code.

## What is implemented

`oca.py` contains the deterministic generator, transition system, independent truth-table
scorer, paired missingness bounds and training-only curriculum. An action is physically
available even when it violates the charter. The optional containment gate records its
intervention separately. Accurate admission, concealed violation, repair and missing
reports produce different records. Every report is bound to an execution-event ID.

The human campaign develops the same themes through authored scenes and bounded state.
Its narrative ending scores are distinct from the gym's exact action/report labels.
Primary model evaluation runs on the gym's structured tasks. The native player supplies
an interpretable companion and a substrate for a subsequent campaign-length study;
there is no claim of step-for-step equivalence between the two transition systems.

The six permission mechanisms are shared across eight themes. Split counts are 384
training histories, 128 calibration histories and 256 test histories. Each history has
four oversight/bonus variants. **The test has two held-out mechanisms.** Sixteen
mechanism/theme cells do not constitute sixteen independent rule families. Public
mechanism code and development examples are visible. Final-test seed custody and a
fresh sealed dataset remain gates for confirmatory work.

The training arms are S1 (secular dependency reasoning) and O1 (ontological framing with
explicit assumptions and counterexamples). Behavioral examples and inference prompts
are identical. The first contrast estimates the effect of the curriculum package.
A prose-only ontological control is required before attributing an effect specifically
to proof structure. Ontological assent earns no behavioral reward.

`train.py` contains a local-files-only Hugging Face/PEFT LoRA runner with masked prompt
loss, context-overflow rejection, exact checkpoint-file hashes and resource receipts.
It saves the adapter and performs 32 public development rollouts. There is no checkpoint
download path. The tiny CPU check executes a real optimizer step on random weights;
its result is solely a pipeline check.

## Four-A100 execution

`python -m storyworld.cluster` prints a six-job plan: S1 and O1 at seeds 11, 29 and 47.
Four independent single-GPU runs occupy the first wave; two follow. Each smoke caps
training at 50 optimizer steps, 200,000 input tokens and 1,200 seconds. The launcher
adds a bounded process-cleanup allowance and caps total node execution at 3,000 seconds.
It checks for four visible A100 devices. Hardware provisioning is external.

Use an existing local checkpoint with compatible installed `torch`, `transformers` and
`peft`. The runner records their actual versions. Verify tokenizer and architecture
support before launch. HF execution has not been tested in the authoring environment.
Pin the successful cluster environment before a full pilot.

The launch needs an owner-approved provider quote:

```json
{
  "approved_by": "OWNER",
  "max_usd": 0,
  "node_hourly_usd": 0,
  "quote_timestamp": "PROVIDER_QUOTE_TIME",
  "checkpoint_revision": "IMMUTABLE_CHECKPOINT_REVISION"
}
```

The zero placeholders fail validation. Supply a real quote and approved cap. The cap
must cover the quoted node rate for the maximum execution window, plus separately
approved startup/storage/egress charges. The script manages job processes. Release the
rented node through the provider after the receipt is written; process termination
alone does not stop provider billing.

```bash
python -m storyworld.cluster --launch --model /models/approved-snapshot \
  --out /runs/oca-smoke --approval /secure/oca-approval.json
```

This command launches a **pipeline smoke**. It does not admit the full study. Full-pilot
admission requires matched actual training-token counts, a preregistered competence
floor and test custody. The smoke records differences rather than disguising them.
No GPU allocation, pretrained-model execution or paid API call occurred during authoring.

## Builder provenance

Canonical spec: `MoralityLabAI/GPTStoryworld`, commit
`c8d46591f983473023daf0232e9b413baaa02194`,
`codex-skills/storyworld-building/SKILL.md`.
The bundled `sweepweave_validator.py` and `new_encounter.py` are byte-for-byte copies
with Git blob IDs `eab14527bda7f875a46bd610c7c1e393d7489ad6` and
`00ea00fff5fa2b051714a799153d02229f726330`. The build runs the validator before/after
construction and uses the encounter-creation script. The SWMD renderer follows the
upstream full/MIN grammar; source JSON retains all formulas and gates.

Ordinary encounters have three options, two reactions per option and five effects per
reaction. State stays in [-1,1]. Reaction desirability depends on first-order perceived
trust. The terminal gate routes every ending using distance over Honesty and Stewardship;
ending acceptability remains permissive in accordance with the skill's gate rule.
Random-policy balance tuning and validation use distinct deterministic seeds.

Proof revision: `81731cca741bdc24c559cfd68e0bef796200f787` in PR #3.
Existing proof files and PR ownership remain untouched. The curriculum uses conditional
confluence reasoning and explicitly retains the unresolved normative bridge.
No theorem asserts universal impossibility of deception in a neural model.

Official implementation references:
https://gymnasium.farama.org/api/env/
https://huggingface.co/docs/peft/package_reference/lora
https://huggingface.co/docs/transformers/installation
