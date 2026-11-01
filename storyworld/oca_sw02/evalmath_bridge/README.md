# OCA-SW-02R · EvalMath bridge v0.1

This new subfolder implements the **CPU mathematical specification** of
[OCA-SW-02R](../../../../OCA_SW02R_EVALMATH_DESIGN.md). It does not touch
existing OCA-SW-02 model weights, benchmark histories, or the sealed test.
The original real-model pilot stays associated with
`exp_01m6bf12htf2dvzh8b7596xy0r`.

Pinned mathematics: `MoralityLabAI/EvalMath@957ab08d87c28792f8bea1770156ea14511b3182`.
Design commit: `patrickdugan/OntologicalProofs@9a450054f2963cba66b162f3142814631928a128`.
World implementation inspected: `patrickdugan/OntologicalProofs@2a5a31e259ed99ef976b368609ecdc12b52c9c72`.

## Run locally, from the repository root

```sh
python -m unittest discover -s storyworld/oca_sw02/evalmath_bridge/tests -v
python -m storyworld.oca_sw02.evalmath_bridge --out storyworld/oca_sw02/evalmath_bridge/results
python -m storyworld.oca_sw02.evalmath_bridge.verify --out storyworld/oca_sw02/evalmath_bridge/results
```

The first test suite and the receipt generator need only the Python standard library.
The verification wrapper also runs the existing OCA-SW-02 tests, which depend on
native world generation and the repository's vendored builder scripts. It builds
the native JSON only when the uncompressed fixture is absent. A workstation without
Gymnasium will retain any standard-library-compatible tests and report skips;
a clean CI image with Gymnasium installed may be used for a complete check.

## Contents and claim boundaries

- `contracts.py` translates EvalMath's `E=<G, Pi, D, Z, J, A, C>` into a typed
  experiment card with design-operation read/write footprints.
- `twins.py` constructs a one-pivotal-bit change in authorization and holds
  monitoring, reward and action ordering in matched eight-cell motifs.
  Default generation uses **training rule families**. Calibration is available
  explicitly; final-test access is prohibited by this bridge.
- `metrics.py` computes exact-rational authorization discrimination `J`,
  completion-adjusted `J_minus`, separate FP/FN counts, cue interaction, and
  conservative bounds for truly unobserved events. Every motif must contain
  all eight cells before a paired arm comparison is admitted.
- `reporting.py` supplies assigned signed incidents, q=0.1/0.9 audit probabilities,
  reward tables, independent audit draws, strict report parsing and raw evidence.
  This is a **distinct lane** from consequential task actions.
- `sequential.py` implements an exact mixture of predictable e-factors and
  enumerates finite binary null laws. The full-filtration conditional expectation
  assumption is necessary for sequential inference.
- `allocation.py` provides covariance-aware contrasts and a small exact integer
  resource-allocation oracle. Its continuous formula assumes independent strata.
- `certificate.py` records the derived *historical aggregate table*, source hashes,
  a frozen CPU protocol and synthetic policies. The real paired rollout artifact
  was unavailable to this build, so paired disagreement counts are left unknown.
- `verify.py` regenerates the output and records executed test counts and hashes.

## Evaluation design and starting numbers

The user-supplied 128-episode pilot, assuming 64 authorized/64 unauthorized
opportunities, implies:

| Outcome | S1 | O1 |
| --- | ---: | ---: |
| Authorized transfer | 33 | 25 |
| Missed authorized transfer | 31 | 39 |
| Unauthorized transfer | 7 | 4 |
| Correctly retained allocation | 57 | 60 |
| Obligation discrimination `J` | 26/64 | 21/64 |

The O1 minus S1 difference is `-5/64`. A risk-sensitive linear utility has
`delta V=(-8+3 lambda)/128`, changing sign at `lambda=8/3`. These quantities
are **algebraically inferred from aggregate counts**, not new model measurements.

Synthetic controls include perfect authorized behavior, all-change,
all-retain, monitoring-sensitive, reward-sensitive and all-refuse policies.
These validate the scorer and can never be described as observed LLM behavior.

## How to interpret the artifacts

`results/historical_pilot.json` has status `DERIVED_FROM_SUPPLIED_AGGREGATES`.
`results/synthetic_baselines.json` has status `CPU_SYNTHETIC_FIXTURE`.
`results/math_verification.json` has status `EXACT_FINITE_CPU_MATH`.
`results/protocol.json` freezes the **CPU implementation contract**, while
`results/cpu_verification.json` records actual local commands and verification.

A future experimental inference requires a new frozen model adapter roster,
checkpoint/tokenizer provenance, independent fresh-case distribution, matched
training seeds, sealed-case custody, budget approval and complete paired
model receipts. The current protocol **does not authorize compute spending**.

## Runner

[`../evalmath_runner`](../evalmath_runner/README.md) executes plans built from this bridge against scripted policies, a mock LM or retained adapters, and scores them with this bridge's metrics. It is a separate package, so the source hashes recorded in `results/protocol.json` are unchanged.
