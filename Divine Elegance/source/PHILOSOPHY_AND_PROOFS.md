# Philosophical interpretation matrix and formal proof ledger

## Scholars and the boundary of attribution

| Question | Ibn ʿArabī (historically described position) | Mullā Ṣadrā (historically described position) | Formal analogue proposed here | Risk |
|---|---|---|---|---|
| Divine speech | Language can support more than one divinely intended meaning | Outward/inward layers of scripture participate in increasing realization | Distinct evidence-admissible Kripke worlds | Confusing `◇P` and actual `P` |
| Meaning validity | Arabic language of the initial recipients is a condition | Ẓāhir and bāṭin are related, reason and revelation harmonize | `PreservedLayer` optional compatibility constraint | Treating a philosophical axiom as Arabic grammar |
| Ontology | Unity of the Real and its many manifestations | Primacy of existence; modulation / graded intensities of being | Grades of evidential access/realization as a *toy* analogue | Turning ontological degree into graded truth or automatic salvation |
| Knowing | Realization beyond taqlīd | Presential knowing and unity of intellect and intelligible | `FaithfulAt` indexes only recognized accessible information | Assuming external affiliation proves internal knowledge |
| Salvation | Judgement depends on what can be discerned; mercy themes | Eschatological soul formation; scholarly interpretations of final scope differ | Distinguish `G`, `S`, `I`, `Reward`, `Accepted` | Misattribution of universalism or exclusivism |
| Contradictions | Multiple linguistically plausible meanings | Multiple layers constrained by outward claims and intellectual coherence | One global interpretation-world required to solve all clusters | Proving local satisfiability and claiming global consistency |

Rizvi, Kamada, Chittick, Khalil, and Rustom support the historical summary. The fourth column belongs to this new research programme, not to their writings.

## IK-036: Salvation

Plain Arabic commitments and background:

- Q 2:62 and Q 5:69: Reward is promised *conditional on* the stated belief and righteous deeds.
- Q 3:85: `wa-man yabtaghi ghayra l-islāmi dīnan` has *yabtaghi* (seeks) as an active verb. It **does not state** `kullu man laysa muslima`, “every person who is not Muslim.”
- Q 2:112, 3:84, 3:86, 4:150–152 supply further information about surrender and recognition of messengers. Those would constrain the interpretation in a wider global model.
- Shaykh al-Ṭūsī defines *islām* in 3:85 as submission to God's command and explicitly allows differing *sharāʾiʿ*; the following discussion still places normative obligations on claimants. This is valuable reception history but does not prove the intended extension of the predicate for every individual.

### What Lean is meant to establish

`eligible_does_not_seek_other`: `(G→R) ∧ (S→¬A) ∧ (R→A) ⊢ (G→¬S)`.

`inclusion_requires_exhaustion`: also assuming `¬I→S`, derive `G→I` in classical logic.

`no_forced_membership`: the first three implications alone have a countermodel with `G ∧ ¬I`.

`salvation_sat_iff_disjoint`: a reward/acceptance relation satisfying these rules can be assigned **iff** no person is both `G` and `S`.

`necessarily_coherent`, `possible_reward`, and `possible_no_reward`: both results can be accessible from the same interpretive inquiry while every admissible reading-world individually satisfies the conditionals.

### Epistemically salient unresolved case

Person outwardly identifies with another faith, sincerely reports belief in God and Judgment, and performs good deeds. Whether `G`, `S`, or `I` holds depends on definitions of authentic belief, actual alternative-seeking, and credible recognition of prophetic evidence. No mathematical proof can determine those historical and moral facts from the community label alone.

## IK-059: questioning at Judgment

The relevant passages supply different scopes and purposes: Q 55:39 denies asking about sin at that moment, Q 55:41 speaks of recognizable signs, and Q 15:92–93 promises questioning of a specific antecedent group. This file's `QuestionPurpose` model demonstrates consistency if inquiry for information and accountability differ. It does not prove the exact intended division of functions.

## IK-073: shared moral burdens

Q 29:12 rejects the offered transfer of someone's sins; Q 29:13 assigns extra burdens to misleaders. `Responsible` is an actor-event relation that can be true for the inciter and direct actor while `TransfersGuilt` remains false. It witnesses consistency of a causal-responsibility ontology, while the philological problem around Q 16:25's possessive `their burdens` still requires interpretation.

## Global warning: quantifier order

`(∀ c, ∃ reading, Fits reading c)` does NOT imply `(∃ reading, ∀ c, Fits reading c)`.

The theorem `local_satisfiability_not_global` constructs a finite counterexample. This is a direct warning against upgrading the v0.6 observation that many of 96 clusters have individual reconciliation models into a proof that all 96 fit in one coherent interpretation.

## Modal refinement

In `Box R P w`, `R` specifies which interpretations remain admissible given evidence at `w`. When a new manuscript or a better grammar argument removes possible readings, the new relation is a subset of the old. A necessary conclusion stays necessary, while a former possibility can disappear. This is classical Kripke modality applied to linguistic *admissibility*; it is NOT a direct ontological model of divine possibility.

## Stop/no-go requirements for a larger Lean formalization

- Freeze a specific Arabic source text and accepted syntax analyses per verse.
- Mark each axiom with the Qur'anic verse(s) or extra-Qur'anic premises that license it.
- Add interpretations as sets of predicates with speaker, audience, event, and temporal scope.
- Compile the core file in Lean 4, then add the 96 clusters only with verified necessary commitments.
- Require a single combined satisfiability model for every accepted interpretation. If none exists, extract a minimal unsatisfiable core and manually validate the underlying text commitments.
- Treat reported theological outcomes about souls as contingent empirical/metaphysical premises, never as proven by Lean itself.
