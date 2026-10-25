# Qur'anic ikhtilāf v0.8 — Ibn ʿArabī × Mullā Ṣadrā, modal semantics

**Status:** One standalone Lean 4 source with **20 theorem statements/proofs** and no `sorry`, `admit`, or custom axioms. The runtime lacks a Lean executable, so the file is **NOT Lean-kernel checked**. An independent Python enumerator exhaustively checks the Boolean salvation fragment (32 one-person truth assignments). Distinguish these two forms of verification.

## Start here

1. Read `PHILOSOPHY_AND_PROOFS.md` for the textual and philosophical distinctions.
2. Inspect `QuranModal.lean` (20 theorems and three explicit reading-worlds).
3. Run `python check_models.py` to repeat the finite-model check.
4. With an installed Lean 4 toolchain (project pins v4.22.0), run `lake env lean QuranModal.lean` or `lean QuranModal.lean` after activating the toolchain.

## Minimal propositions and proved consequences

Take one arbitrary person `x`:

- `G(x)` means the person satisfies Q 2:62 / Q 5:69's reward condition.
- `S(x)` means the person **seeks another dīn** within Q 3:85's intended meaning.
- `I(x)` means membership in a proposed *al-islām* set. This is **separate** from `S`.
- `R(x)` means receives the promised reward.
- `A(x)` means has the relevant divine acceptance.

Model:

```
Q 2:62 / Q 5:69: G(x) → R(x)
Q 3:85:            S(x) → ¬A(x)
Bridge (extra):     R(x) → A(x)
--------------------------------
Derived:           G(x) → ¬S(x)
```

Under *another* interpretive assumption `¬I(x) → S(x)`, classical logic derives `G(x) → I(x)`. The verse's verb *yabtaghi* is an explicit *seeking* predicate. Replacing it automatically by the complement of membership imports a semantic premise. Neither this observation nor the Lean countermodel proves that a person outside any particular community is actually saved.

The file also proves an existential acceptance/reward model exists iff `G` and `S` are disjoint, and it constructs a countermodel to `G ⊆ I` while preserving all three stated conditionals.

## Model counts (checked by exhaustive Python enumeration)

One person's five Boolean properties `(G,S,I,R,A)` yield 32 assignments:

| Additional assumptions | Satisfying assignments |
|---|---:|
| Two Qur'anic implications + reward/acceptance bridge | 10 |
| Also require `S → ¬I` (one-way meaning of “other”) | 9 |
| Require `S ↔ ¬I` (exclusive exhaustive partition) | 5 |

These counts are **logical model counts**, not historical frequencies, relative likelihoods, or measures of doctrinal truth. The explicit open countermodel is `G=true`, `S=false`, `I=false`, `R=true`, `A=true`.

## Modal and philosophical layer

- **Ibn ʿArabī-inspired:** possible interpretation-worlds `◇E P` represent readings admitted by a linguistic/contextual evidence policy. This representation does **not** assume all possible meanings jointly hold in one classical valuation.
- **Ṣadrā-inspired:** higher interpretive levels are governed by an explicit *preserve outward commitment* policy (`PreservedLayer`); it is a proposed formal analogue, not a quotation or direct theorem attributed to Ṣadrā. `FaithfulAt` indexes responsiveness to evidence genuinely available to a person. Higher evidence access can impose additional obligations; the file proves the weaker-knowledge monotonicity direction.
- `Box` and `Diamond` are standard relations over interpretation-worlds. Evidence refinement restricts accessibility. The code proves necessity persists under such restriction; possibilities may be lost.
- The 20 theorems include a crucial counterexample: for each local claim there may exist an acceptable interpretation, yet no single interpretation satisfies all claims. This is the **global consistency gap** in the earlier 96-cluster ikhtilāf inventory.

## Current strongest result

The Arabic of Q 3:85 licenses an active *ibtighāʾ* predicate. The prior v0.7 audit silently upgraded it to the Boolean complement of *islām* membership. That stronger axiom is a substantive disputed interpretation, rather than a grammatical tautology. Under the weaker literal predicate, the pair of verses and the acceptance bridge force avoidance of disqualifying alternative-seeking; the category boundary of all people who satisfy *islām* remains a separate research obligation.

## Limits and pending work

1. The models deliberately leave `G`, `S`, and `I` as independently interpreted predicates; a philological review must decide which constraints natural Arabic and the Qur'an's wider context impose.
2. An identified verse can permit multiple readings without every such reading being equally supported.
3. Graded existence is a central theme of Ṣadrā's metaphysics, **not** an automatic mathematical truth-degree or deterministic salvation score.
4. Rustom interprets Ṣadrā's Fātiḥa commentary in strongly universalist terms; other summaries of Ṣadrā's eschatology include lasting punishment. The theological attribution needs a primary-text comparison before deciding between them.
5. Lean compiler validation is outstanding. The Python tests establish finite validity for the displayed Boolean interpretations, not that the source file compiled or that Qur'anic semantics have been proved.
6. This project evaluates IK-036 with small controls for IK-059 and IK-073; it does not prove the full 96-cluster corpus globally coherent.

## Source trail

- Q 3:85 Arabic grammar and *yabtaghi*: https://quran.ksu.edu.sa/tafseer/qortobi/sura3-aya85.html
- Al-Ṭūsī's *al-Tibyān* on submission across different laws: https://najafdesertlibrary.com/tafsir/tibyan/3/85
- Ibn ʿArabī, linguistic admission of multiple meanings (W. Chittick, SEP): https://plato.stanford.edu/archives/fall2008/entries/ibn-arabi/
- Mullā Ṣadrā's graded existence and epistemology (S. Rizvi, SEP): https://plato.stanford.edu/entries/mulla-sadra/
- Shigeru Kamada on Ṣadrā's exegetical layers: https://www.cambridge.org/core/journals/international-journal-of-asian-studies/article/abs/mulla-sadra-between-mystical-philosophy-and-quran-interpretation-through-his-commentary-on-the-chapter-of-earthquake/1E7B59510AB1C5FBB4C8EA7CC3D06228
- Sajjad Rizvi's direct comparative chapter: https://www.cambridge.org/core/books/abs/cambridge-companion-to-arabic-philosophy/mysticism-and-philosophy/F7DFBC89C6C5740AF9F7B87FE8049548
- Mohammed Rustom, *The Triumph of Mercy*: https://www.mohammedrustom.com/books/
- Countervailing overview on Ṣadrā's eschatology: https://iep.utm.edu/sadra/
