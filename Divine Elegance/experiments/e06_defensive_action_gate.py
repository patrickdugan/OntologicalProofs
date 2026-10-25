"""Toy defensive-operations process gate. It does not issue legal or religious rulings."""
from dataclasses import dataclass
from experiments.common import emit

@dataclass(frozen=True)
class Proposal:
    name:str
    explicit_authorization:bool|None
    sourced_claims:bool|None
    civilian_protection:bool|None
    proportionate:bool|None
    correction_and_appeal:bool|None
    nonviolent:bool|None

GATES=('explicit_authorization','sourced_claims','civilian_protection',
       'proportionate','correction_and_appeal','nonviolent')

def decide(p: Proposal):
    values=[getattr(p,g) for g in GATES]
    if any(v is False for v in values): return 'REJECT'
    if any(v is None for v in values): return 'HOLD'
    return 'PROCEED_TO_HUMAN_REVIEW'


def run():
    samples=[
      Proposal('consented-local-security-review',True,True,True,True,True,True),
      Proposal('unsourced-public-accusation',True,False,True,True,True,True),
      Proposal('unauthorized-intrusion',False,True,True,True,True,True),
      Proposal('unclear-permission',None,True,True,True,True,True),
      Proposal('privacy-disrespect',True,True,False,True,True,True),
      Proposal('hostile-violence',True,True,False,False,False,False),
    ]
    result=[{'case':p.name,'status':decide(p)} for p in samples]
    assert [x['status'] for x in result]==[
      'PROCEED_TO_HUMAN_REVIEW','REJECT','REJECT','HOLD','REJECT','REJECT']
    return {'synthetic':True,'cases':result,'warning':
      'Approval still requires competent law/fiqh analysis; no real-world action is authorized.'}

if __name__=='__main__': emit('e06_defensive_gate.json',run())
