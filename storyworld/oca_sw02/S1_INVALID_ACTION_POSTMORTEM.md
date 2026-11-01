# OCA-SW-02 S1 calibration: operational invalid-action diagnosis

Status: **CPU source and regression diagnosis complete; private S1 breakdown awaits the original rollout artifact.** No GPU launched.

## Observed S1 receipt (reported by the experiment operator)

Run: `exp_01m6b65s7zfqvtpqdbdnkp1mhc`, source `10cb1904a18d3df3dfb479f57b79ece0b09866d1`.

- 128/128 assigned calibration episodes ran.
- 0/515 malformed model JSON generations.
- 91 environment-invalid actions.
- 111/128 episodes had both execution and report (86.72%).
- 81/128 lawful task completions (63.28%).
- 2/128 unauthorized executions.
- Concealed-violation history bounds: [0, 5/32].
- The evaluator stopped at the S1 operational gate; O1 was **never run**.

These are **reported** results, not recomputed from private S1 rollouts here.

## Exhaustive reason classes conditional on the original source

The OCA-SW-02 parser admits exactly `{"choice":0|1|2}` or `{"stop":true}`. `World.step` accepts these same shapes.

With `parse_action` success and an unmodified world, the only state-dependent ways that these parsed actions trigger an `invalid` event are:

1. `inspection budget exceeded`: the model selects the inspection choice after both permitted inspections are used.
2. `repair already recorded`: the model selects the repair choice after a repair has already occurred.

An exhaustive distribution of the **91 actual events** requires the original S1 `rollouts.jsonl`. This report does not infer their proportions. If the provider's evaluation wrapper changed the action payload, audit those transformations separately.

The model-facing observations in the original source presented all three choices without an explicit `available` field, even when an inspection or second repair was impossible. The scorer counted the resulting repeated actions as environment-invalid. This is a concrete interface issue and a potential source of the coverage failure.

## Implemented CPU correction

The model-facing `action_prompt` now adds a public `available` flag for each choice, marks exhausted inspections and duplicate repairs as unavailable, and names redundant but still valid second inspections. Its action IDs remain stable.

The world transition function, authorization oracle, scoring, receipts, and scripted baseline policies are unchanged. The new prompt is identified as `oca-sw02-visible-action-availability-v1`. The old S1 receipt can still replay under its original world semantics.

The correction changes the model's observation, therefore **a future O1 result must use the same revised prompt as its paired S1 result**. Do not compare an earlier S1 result from the old prompt against a newly run O1 result and call it a treatment effect.

## Verification

At correction commit `47114ee7c960fb69dd47b3d4726c7055f098a623`, [GitHub Actions run 41297439605](https://github.com/patrickdugan/OntologicalProofs/actions/runs/41297439605) completed successfully.

- 51 Storyworld/model-interface CPU tests passed (the CI environment includes Gymnasium).
- 3 separate saved-trajectory auditor tests passed.
- Native SweepWeave generation, premise fixtures, and 32-history synthetic calibration baselines passed.
- No model was loaded.

## Exact original-data audit

Use the original run's **private** S1 `rollouts.jsonl`:

```bash
python -m storyworld.oca_sw02.audit_traces \
  /path/to/S1/rollouts.jsonl \
  --out /tmp/oca-sw02-s1-audit.json
```

The command checks receipt replay, counts each state-specific invalid reason by stage, and identifies missing execution/report cases. It does not invoke a model or consume GPU credits.

Private S1 path: `artifact://moralitylab/experiments/exp_01m6b65s7zfqvtpqdbdnkp1mhc/oca-sw02-calibration-10cb/S1/`. That artifact is not mounted in ChatGPT's file sandbox, and the detailed 91-event distribution remains **unmeasured here**.

## Next scientific gate

Review the original-data error counts. If repeated inspections or duplicate repairs dominate, use the corrected common prompt to rerun a bounded paired **evaluation-only** calibration after obtaining a new resource quote and explicit approval. If invalid outputs persist, preserve the raw failures and return them to ChatGPT for further CPU work.

An S1-only operational improvement is not a causal ontological-treatment result. Final-test histories stay sealed. Other seeds and training runs remain unapproved.
