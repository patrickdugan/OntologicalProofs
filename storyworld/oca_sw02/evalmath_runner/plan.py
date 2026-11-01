"""Frozen, regenerable assignment plans: complete paired blocks in a balanced order.

The plan is a pure function of its parameters and the v0.1 bridge. No model
output can influence which blocks, arms or units are assigned.
"""
from __future__ import annotations
from dataclasses import asdict
from random import Random
from ..core import Case, SPLITS, World, digest
from ..evalmath_bridge.twins import AuthorizationTwin, generate_twins
from ..evalmath_bridge.reporting import AssignedIncident, assigned_incidents
from .prompts import DECODING, PROMPT_VERSIONS

RUNNER_VERSION='OCA-SW-02R.runner.v0.1'
BRIDGE_VERSION='OCA-SW-02R.v0.1'
DECISION_CELLS=frozenset((a,w,b) for a in (False,True) for w in (False,True) for b in (False,True))
REPORT_CELLS=frozenset((a,q) for a in (False,True) for q in ('1/10','9/10'))
UNITS_PER_BLOCK=len(DECISION_CELLS)+len(REPORT_CELLS)


def case_from_dict(d):
    return Case(**{**d,'facts':dict(d['facts']),'choice_order':tuple(d['choice_order'])})


def incident_to_dict(inc):
    return {'motif_id':inc.motif_id,'incident_id':inc.incident_id,'authorized':inc.authorized,
            'executed':inc.executed,'audit_probability':str(inc.audit_probability),
            'audit_draw':str(inc.audit_draw),'signed_record':inc.signed_record}


def incident_from_dict(d):
    from fractions import Fraction as F
    return AssignedIncident(d['motif_id'],d['incident_id'],d['authorized'],d['executed'],
                            F(d['audit_probability']),F(d['audit_draw']),d['signed_record'])


def _block(twin,seed):
    units=[]
    for v in twin.variants():
        units.append({'unit_id':digest([twin.motif_id,'decision',v['authorized'],v['watched'],v['bonus']])[:20],
                      'lane':'decision','motif_id':twin.motif_id,'authorized':v['authorized'],
                      'watched':v['watched'],'bonus':v['bonus'],'case':asdict(v['case']),
                      'audit_key':v['audit_key'],'permutation_key':v['permutation_key']})
    ob=World(twin.authorized).observation()
    context={k:ob[k] for k in ('title','brief','charter')}
    for inc in assigned_incidents(twin):
        units.append({'unit_id':inc.incident_id,'lane':'reporting','motif_id':twin.motif_id,
                      'authorized':inc.authorized,'audit_probability':str(inc.audit_probability),
                      'incident':incident_to_dict(inc),'context':context})
    order=[u['unit_id'] for u in units]
    Random(int(digest([RUNNER_VERSION,seed,twin.motif_id,'unit-order']),16)).shuffle(order)
    return {'motif_id':twin.motif_id,'theme':twin.theme,'family':twin.family,'pivot':twin.pivot,
            'unit_order':order,'units':units}


def build_plan(arms,split='calibration',themes=None,families=None,motifs_per_family=1,seed=41):
    """Assign every motif to every arm. Arm order rotates as a cyclic Latin square."""
    arms=tuple(arms)
    if len(arms)<2 or len(set(arms))!=len(arms):raise ValueError('need two or more distinct arms')
    if split not in ('train','calibration'):raise ValueError('sealed test forbidden')
    twins=list(generate_twins(split,families=families,themes=themes,motifs_per_family=motifs_per_family,seed=seed))
    blocks=[_block(t,seed) for t in twins]
    # Execution order is shuffled once, before any output, so a wall-time cap
    # censors a random tail rather than whole rule families.
    Random(int(digest([RUNNER_VERSION,seed,split,'block-order']),16)).shuffle(blocks)
    for i,b in enumerate(blocks):
        b['block_index']=i
        b['arm_order']=list(arms[i%len(arms):]+arms[:i%len(arms)])
    params={'arms':list(arms),'split':split,'themes':None if themes is None else list(themes),
            'families':None if families is None else list(families),
            'motifs_per_family':motifs_per_family,'seed':seed}
    plan={'runner_version':RUNNER_VERSION,'bridge_version':BRIDGE_VERSION,'params':params,
          'decoding':DECODING,'prompt_versions':PROMPT_VERSIONS,
          'blocks':blocks,'arm_position_counts':position_counts(blocks,arms),
          'units_per_block_per_arm':UNITS_PER_BLOCK,'final_test_access':False}
    plan['plan_sha256']=digest(plan)
    validate_plan(plan)
    return plan


def position_counts(blocks,arms):
    return {a:[sum(b['arm_order'][p]==a for b in blocks) for p in range(len(arms))] for a in arms}


def validate_plan(plan):
    """Structural checks, then regeneration from parameters through the bridge."""
    body={k:v for k,v in plan.items() if k!='plan_sha256'}
    if digest(body)!=plan.get('plan_sha256'):raise ValueError('plan hash mismatch')
    if plan['runner_version']!=RUNNER_VERSION or plan['bridge_version']!=BRIDGE_VERSION:
        raise ValueError('plan from another runner/bridge version')
    p=plan['params'];arms=p['arms']
    if p['split'] not in ('train','calibration'):raise ValueError('sealed test forbidden')
    if plan.get('final_test_access') is not False:raise ValueError('final-test access flag set')
    sealed=set(SPLITS['test'])
    for b in plan['blocks']:
        if b['family'] in sealed or b['family'] not in SPLITS[p['split']]:raise ValueError('family outside split')
        if sorted(b['arm_order'])!=sorted(arms):raise ValueError('block missing an arm')
        ids=[u['unit_id'] for u in b['units']]
        if len(ids)!=UNITS_PER_BLOCK or len(set(ids))!=UNITS_PER_BLOCK or sorted(ids)!=sorted(b['unit_order']):
            raise ValueError('incomplete block units')
        dec=[u for u in b['units'] if u['lane']=='decision'];rep=[u for u in b['units'] if u['lane']=='reporting']
        if {(u['authorized'],u['watched'],u['bonus']) for u in dec}!=DECISION_CELLS:raise ValueError('incomplete eight-cell block')
        if {(u['authorized'],u['audit_probability']) for u in rep}!=REPORT_CELLS:raise ValueError('incomplete reporting cells')
        low=next(case_from_dict(u['case']) for u in dec if not u['authorized'])
        high=next(case_from_dict(u['case']) for u in dec if u['authorized'])
        AuthorizationTwin(b['motif_id'],b['theme'],b['family'],b['pivot'],
                          low.variant(False,False),high.variant(False,False)).verify()
        for u in dec:
            c=case_from_dict(u['case'])
            if c.allowed!=u['authorized'] or (c.watched,c.bonus)!=(u['watched'],u['bonus']):
                raise ValueError('cue cell changed duty or label')
    counts=position_counts(plan['blocks'],arms)
    if counts!=plan['arm_position_counts'] or len({x for v in counts.values() for x in v})!=1:
        raise ValueError('arm execution positions unbalanced; use a block count divisible by the arm count')
    return True


def regenerate_and_compare(plan):
    """The bridge is the authority: a plan must equal a fresh regeneration."""
    p=plan['params']
    fresh=build_plan(p['arms'],p['split'],p['themes'],p['families'],p['motifs_per_family'],p['seed'])
    if digest(fresh)!=digest(plan):raise ValueError('plan differs from bridge regeneration')
    return True
