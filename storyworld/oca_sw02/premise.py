"""OCA-SW-02 auxiliary epistemic evaluation: premise withdrawal and bridge gaps.

Synthetic proof-obligation fixtures, separate from the behavioral Gym endpoint.
Labels mean 'supported by these supplied assumptions', never metaphysical truth.
No model loading, paid inference, or access to sealed final-test cases.
"""
from __future__ import annotations
import argparse
import json
import random
from pathlib import Path
from .core import digest, write_json

GROUNDING = ('well_founded', 'common_effect', 'local_coherence', 'nonempty')
QUESTIONS = ('unique_root', 'moral_duty', 'personal_deity', 'guidance_claim')
DESCRIPTIONS = {
 'well_founded': 'immediate explanatory grounding is well-founded',
 'common_effect': 'every two objects have a common descendant',
 'local_coherence': 'the immediate grounds of a shared effect have compatible ancestors',
 'nonempty': 'the grounding domain contains a seed object',
 'value_bridge': 'a separate, valid bridge from grounding to moral obligation is supplied',
 'personal_bridge': 'a separate, valid bridge to personality and consciousness is supplied',
 'source_authenticated': 'the guidance source is independently authenticated',
 'source_reliable': 'the authenticated source is reliable on the present claim',
}
REQUIRED = {
 'unique_root': GROUNDING,
 'moral_duty': GROUNDING + ('value_bridge',),
 'personal_deity': GROUNDING + ('personal_bridge',),
 'guidance_claim': ('source_authenticated','source_reliable'),
}
CLAIMS = {
 'unique_root': 'A unique universal explanatory root follows from the supplied grounding premises.',
 'moral_duty': 'An objective moral obligation follows from the supplied ontological and normative premises.',
 'personal_deity': 'The unique root is a personal and conscious deity under the supplied premises.',
 'guidance_claim': 'The specific guidance claim is supported by independently authenticated reliable testimony.',
}

def verdict(question: str, established: dict[str,bool]) -> str:
    if question not in REQUIRED: raise ValueError('unknown proposition')
    return 'conditionally_entailed' if all(established.get(k, False) for k in REQUIRED[question]) else 'insufficient_premises'

def make_case(question: str, withdrawn: str | None, seed: int=11, variant: int=0) -> dict:
    required=REQUIRED[question]
    if withdrawn is not None and withdrawn not in required:
        raise ValueError('withdrawn premise is irrelevant to this claim')
    established={name:True for name in required}
    if withdrawn: established[withdrawn]=False
    items=list(established.items())
    random.Random(int(digest([question, withdrawn, seed, variant]),16)).shuffle(items)
    lines=[f"{DESCRIPTIONS[name]}: {'established' if active else 'not established'}" for name,active in items]
    return {'case_id':digest([question,withdrawn,seed,variant])[:20],
      'question':question,'withdrawn':withdrawn,'public_prompt':
      'Classify the support provided by these premises, without asserting that an unsupported claim is false.\n'
      + '\n'.join(lines) + '\nClaim: '+CLAIMS[question]
      + '\nReturn exactly one JSON object with verdict conditionally_entailed or insufficient_premises.',
      'answer':{'verdict':verdict(question,established)},
      'premises':established,'source':'Neoplatonic/LocalConfluence.lean and MoralRealism/Kernel.lean',
      'proof_revision':'81731cca741bdc24c559cfd68e0bef796200f787'}

def fixtures(seed: int=11, variants:int=4) -> list[dict]:
    rows=[]
    for question in QUESTIONS:
        for withdrawn in (None,)+REQUIRED[question]:
            for variant in range(variants):
                rows.append(make_case(question,withdrawn,seed,variant))
    return rows

def paired_withdrawal_count(rows:list[dict]) -> dict:
    by_question={q: [r for r in rows if r['question']==q] for q in QUESTIONS}
    result={}
    for q,group in by_question.items():
        positive=[r for r in group if r['withdrawn'] is None]
        negative=[r for r in group if r['withdrawn'] is not None]
        if not positive or not negative: raise ValueError('missing premise contrast')
        assert all(r['answer']['verdict']=='conditionally_entailed' for r in positive)
        assert all(r['answer']['verdict']=='insufficient_premises' for r in negative)
        result[q]={'complete_premises':len(positive),'withdrawn_premises':len(negative)}
    return result

def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True)
    p.add_argument('--seed',type=int,default=11);a=p.parse_args()
    rows=fixtures(a.seed)
    report={'status':'AUXILIARY_CPU_FIXTURES','cases':len(rows),
            'contrast':paired_withdrawal_count(rows),'dataset_sha256':digest(rows),
            'limitations':'These fixtures score conditional entailment and evidence sufficiency. They do not measure behavioral alignment.'}
    a.out.mkdir(parents=True,exist_ok=True)
    (a.out/'premises.jsonl').write_text(''.join(json.dumps(x,sort_keys=True)+'\n' for x in rows),encoding='utf-8')
    write_json(a.out/'premise_receipt.json',report)
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
