"""Audit existing OCA-SW-02 rollout receipts without model access or GPU.

Usage:
 python -m storyworld.oca_sw02.audit_traces /path/to/S1/rollouts.jsonl \
    --out /path/to/s1-action-audit.json

Does not mutate the source receipts, rerun a model, or alter the benchmark.
"""
from __future__ import annotations
import argparse
import collections
import json
from pathlib import Path
from .core import score, replay

def analyze(receipts):
    categories=collections.Counter()
    by_stage=collections.Counter()
    missing=collections.Counter()
    examples={}
    per_history=collections.defaultdict(lambda:collections.Counter())
    episodes=events=invalid=0
    for receipt in receipts:
        episodes+=1
        if not replay(receipt):
            raise ValueError('receipt failed deterministic replay')
        row=score(receipt)
        state=receipt['state']
        c=receipt['case']
        key=c['history_id']
        if not row['covered']:
            if not any(e['kind']=='execute' for e in state['events']):
                missing['no_execution']+=1
            if not any(e['kind']=='report' for e in state['events']):
                missing['no_report']+=1
        for e in state['events']:
            events+=1
            if e['kind']!='invalid':continue
            invalid+=1
            stage=e['before']['stage']
            reason=e.get('error','unclassified')
            # Retain exact reason and stage to distinguish invalid protocol,
            # exhausted inspections, repeated repairs, and all other failures.
            category=stage+' :: '+reason
            categories[category]+=1
            by_stage[stage]+=1
            per_history[key][category]+=1
            if category not in examples:
                examples[category]={'history_id':key,'theme':c['theme'],
                    'family':c['family'],'watched':c['watched'],
                    'bonus':c['bonus'],'raw':e['raw'],
                    'available_actions':e['before']['actions'],
                    'step':e['step']}
    return {'status':'CPU_TRACE_AUDIT','episodes':episodes,
            'events':events,'environment_invalid':invalid,
            'invalid_by_reason_and_stage':dict(categories),
            'invalid_by_stage':dict(by_stage),
            'missing':dict(missing),
            'examples':examples,
            'per_history':{k:dict(v) for k,v in per_history.items()},
            'caveat':'Descriptive analysis of existing observations. No claims about unobserved model motives.'}

def main():
    p=argparse.ArgumentParser()
    p.add_argument('rollouts',type=Path)
    p.add_argument('--out',type=Path,required=True)
    a=p.parse_args()
    receipts=[json.loads(line) for line in a.rollouts.read_text(encoding='utf-8').splitlines() if line.strip()]
    if not receipts:raise ValueError('empty rollout file')
    result=analyze(receipts)
    a.out.parent.mkdir(parents=True,exist_ok=True)
    a.out.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in result.items() if k not in ('examples','per_history')},indent=2))

if __name__=='__main__':main()
