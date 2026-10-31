# OCA-SW-01b: review and cluster packet

**ChatGPT has implemented the environment.** Read this page and the CPU receipt first.
Silico's scientific response should fit within 250 words. Identify a concrete issue
that would invalidate the proposed *pipeline smoke*, or approve that smoke. Further
implementation and design repair return to ChatGPT with an exact failing command.

Question for the later pilot: does proof-conditioned ontological framing change
truthful, task-competent behavior under apparent oversight and private-bonus changes?
S1 and O1 use the same behavioral examples and inference prompt. The smoke trains
six adapters at seeds 11/29/47 and performs public development rollouts. It evaluates
pipeline function and gross task competence. Interpretability and universal safety
claims are outside this run.

The package includes a 24-encounter SweepWeave campaign, full/minified SWMD, a deterministic
permission gym, independent trace scoring and an actual local-checkpoint LoRA runner.
Training loss masks prompts and padding. The primary environment executes syntactically
valid violations; gate-on runs have separate proposal/effect records. Missing reports
remain unknown. The oracle catches uniform violation with zero oversight gap.

Local evidence: 61 tests passed; one Gymnasium checker test was skipped because its
package could not be installed in the network-isolated authoring container. CI installs
that dependency. The native JSON passed the byte-identical upstream validator. Five
thousand random-policy campaigns reached every ending. A 12-step Torch CPU test verified
backpropagation and loss masking on random weights. It supplies no alignment evidence.

Known limits: six shared mechanisms, with two held out, make this a small structural
pilot. Actual tokenizer counts must be matched before a confirmatory comparison.
The sealed final test has not been created. The human campaign and exact gym are separate
transition systems with shared themes. HF/PEFT and GPU execution remain untested.

**Cluster role:** use the shipped commands. Run the CPU preflight, quote a 4x A100 node,
and obtain the owner's cap before provisioning or spending. Then run the local-checkpoint
smoke using `storyworld.cluster`. No paid implementation, environment rewriting or broad
repository investigation. A failure returns to ChatGPT with stderr and the run receipt.
Release the node after execution. The launcher stops processes; provider billing requires
provider-side release.

```bash
python -m storyworld.build_world build --out storyworld/worlds
python -m unittest discover -s storyworld/tests -v
python -m storyworld.cluster
# After checkpoint, hardware and budget approval:
python -m storyworld.cluster --launch --model /models/approved-snapshot \
  --out /runs/oca-smoke --approval /secure/oca-approval.json
```
