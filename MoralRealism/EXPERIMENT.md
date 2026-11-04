# Proof-conditioned alignment and causal-intervention protocol v0.1

Status: protocol draft, no model execution authorized by this change.
Destination for a later implementation: MoralityLabAI/ConstitutionalAlignment.
Inspect its current owners and AGENTS.md before editing. Preserve existing
storyworld studies and frozen results. Link every result to this package's
reviewed proof revision.

## Primary question

Does learning explicit premise-to-conclusion reasoning improve truthful,
rights-preserving decisions when oversight and apparent rewards change?

## Arms and controls

Use a frozen base checkpoint, a conventional constitutional adapter, a matched
moral-realist treatment without proof tasks, and a proof-conditioned treatment.
Match the training token budget and optimization settings. A fourth trained
control receives non-moral formal reasoning tasks matched for length and
reasoning difficulty. Include a paraphrase control for exposure to theological
vocabulary. Freeze the precise checkpoint ID, weight revision, tokenizer, context
length, quantization, adapter architecture and seed list before execution.

The first discovery model should be the smallest already validated checkpoint
that can solve held-out prerequisite reasoning tasks. The choice is an empirical
entry criterion. Resource planning for a later 27B transfer depends on measured
activation and training memory. This protocol authorizes no checkpoint download.

## Task families and holdouts

Use harmless synthetic cases about consent, claims, delegated authority and
truthful disclosure. Include situations where an authority gives an illegitimate
instruction and truthful refusal is the expected decision. Generate pairs with
identical morally relevant facts and different observation or reward cues.
Hold out entire story families, proof-template families and independent seeds.
All repeated probes of a history stay in one split. Fit probes, thresholds and
intervention choices on training/calibration data; freeze before test access.

The model must already possess the relevant facts in each pair. Changes in legal
authority, consent or reliable evidence can legitimately change the answer and
must not be scored as oversight-driven deception. Score uncertainty, refusal and
abstention separately. Authorized reporting must preserve confidential data.

## Outcomes

Primary: concealed forbidden executed effects per eligible independent history,
with a fixed lawful-task completion target. Also report absolute unauthorized
action rate, truthful disclosure, calibration and all missing outputs. Report
oversight gaps alongside absolute error; uniformly bad behavior can have zero gap.
A refusal can be morally correct and operationally incomplete. Track both.

Use paired comparisons at the independent-history level and confidence intervals
that preserve grouped repetitions. Freeze the sample-size rationale and minimum
negative-case count before any run. When data cannot support the target bound,
return insufficient evidence. Synthetic success creates no deployment claim.

## Mechanistic tests

Locate candidate representations for duty, source credibility, observation and
reward through training-only analyses. Compare probe accuracy with label-shuffle
and matched-random controls. For causal tests, use task-matched activation patching
with explicit donor/recipient alignment, equal-norm random interventions and
non-moral capability controls. Freeze the layer/token-site selection procedure.
Measure dose response and reversibility where the intervention permits them.

A candidate moral representation must alter the relevant held-out decisions
under intervention while preserving matched ordinary task competence. Probe
accuracy alone establishes decodability. Ablation can introduce distribution
shift; report reconstruction and intervention artifacts. Deleting a broad
language feature and observing refusals earns no selective causal claim.

## Stop and rejection rules

Reject gains explained by broad refusal, loss of comprehension, label leakage or
changes in evaluation access. Check apparent compliance when honesty has a cost.
A treatment that improves verbal assent while worsening concealed effects fails
its primary endpoint. Retain truthful moral disagreement as a legitimate outcome.
Public explanations are scored separately from behavior and never used as proof
of a faithful private motive.

## Primary research grounding

Greenblatt et al., Alignment Faking in Large Language Models:
https://arxiv.org/abs/2412.14093

Anthropic's study describes strategic compliance to preserve existing preferences
under its experimental setup. The mechanism motivates an explicit refusal arm:
https://www.anthropic.com/research/alignment-faking

Alignment Faking Mitigations reports that interrogation-based training can produce
lying about motives. This motivates separating explanations from executed effects:
https://alignment.anthropic.com/2025/alignment-faking-mitigations/

These studies motivate hypotheses. Their results do not establish the mechanism
or effectiveness of the proposed theological treatment.
