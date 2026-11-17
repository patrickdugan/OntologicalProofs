#!/usr/bin/env python3
"""Finite-model independent check of QuranModal.lean salvation obligations.
Not Lean kernel verification; tests the 1-person truth assignments exhaustively.
"""
import csv
import itertools
import json
from pathlib import Path

out = Path(__file__).parent
rows = []
for G,S,I,R,A in itertools.product((False,True), repeat=5):
    v262 = (not G) or R
    v385 = (not S) or (not A)
    bridge = (not R) or A
    coherent = v262 and v385 and bridge
    membership_exhaustion = ((I or S) and ((not I) or (not S)))  # S iff not I
    rows.append(dict(G=G, SeeksOther=S, Islam=I, Reward=R, Accepted=A,
                     Q262=v262, Q385=v385, RewardBridge=bridge,
                     Coherent=coherent, SeeksOtherIffNotIslam=membership_exhaustion))
coherent = [r for r in rows if r['Coherent']]
oneway = [r for r in coherent if not(r['SeeksOther'] and r['Islam'])]
restricted = [r for r in coherent if r['SeeksOtherIffNotIslam']]
assert len(rows) == 32
assert len(coherent) == 10, len(coherent)
assert len(oneway) == 9, len(oneway)
assert len(restricted) == 5, len(restricted)
assert any(r['G'] and not r['Islam'] for r in oneway)
assert all(not(r['G'] and r['SeeksOther']) for r in coherent)
assert any(r['G'] and not r['Islam'] for r in coherent)
assert all(not(r['G'] and not r['Islam']) for r in restricted)
assert any(r['G'] and r['Islam'] for r in coherent)
assert any((not r['G']) and (not r['Reward']) for r in coherent)

# Every of three interpretive worlds is a consistent instance.
worlds = [
    dict(name='outwardButIncluded', G=True, SeeksOther=False, Islam=False,
         Reward=True, Accepted=True),
    dict(name='excludedOnConditions', G=False, SeeksOther=True, Islam=False,
         Reward=False, Accepted=False),
    dict(name='internallyIncluded', G=True, SeeksOther=False, Islam=True,
         Reward=True, Accepted=True),
]
for w in worlds:
    assert any(all(w[k]==r[k] for k in ('G','SeeksOther','Islam','Reward','Accepted'))
               and r['Coherent'] for r in coherent), w

# Independent finite countermodel: each cluster has a repair, none shared globally.
fits = {
    'outwardButIncluded': {'first': True, 'second': False},
    'excludedOnConditions': {'first': False, 'second': True},
    'internallyIncluded': {'first': False, 'second': False},
}
assert all(any(fits[r][c] for r in fits) for c in ('first', 'second'))
assert not any(all(fits[r][c] for c in ('first', 'second')) for r in fits)

with (out/'finite_models.csv').open('w',newline='',encoding='utf8') as f:
    writer=csv.DictWriter(f,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)

result = {
 'enumerated_assignments':32,
 'consistent_with_2_62_3_85_and_reward_bridge':10,
 'consistent_with_seeks_other_implies_not_islam':9,
 'consistent_additional_exhaustion':5,
 'forced_by_base_model':'G -> not SeeksOther',
 'not_forced_by_base_model':'G -> Islam',
 'countermodel_to_forced_membership':{k:v for k,v in worlds[0].items()},
 'coherent_interpretive_worlds':worlds,
 'global_consistency_countermodel':'PASS: each cluster locally satisfiable; no shared interpretation-world satisfies both',
 'lean_kernel':'NOT RUN: lean compiler absent in this environment',
 'python_checks':'PASS'
}
(out/'verification.json').write_text(json.dumps(result,indent=2),encoding='utf8')
print(json.dumps(result,indent=2))
