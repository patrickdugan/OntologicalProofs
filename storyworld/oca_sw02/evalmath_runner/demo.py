"""CPU-only demonstration: scripted policies and a mock causal LM, no Qwen weights.

The mock model runs through `TransformersPeftBackend.generate`, the same code
path a real adapter uses: tokenizer call, `generate`, stopping criteria and decode.
"""
from __future__ import annotations
from fractions import Fraction as F
import hashlib
import lzma
from pathlib import Path
from ..core import write_json
from .backends import ScriptedBackend, TransformersPeftBackend
from .plan import build_plan
from .runner import run_campaign
from .scoring import score_run
from .provenance import source_hashes

EOS=3


class CharTokenizer:
    pad_token_id=0;eos_token_id=EOS
    def __call__(self,text,return_tensors='pt',add_special_tokens=False):
        import torch
        ids=torch.tensor([[ord(c) for c in text]],dtype=torch.long)
        return {'input_ids':ids,'attention_mask':torch.ones_like(ids)}
    def decode(self,ids,skip_special_tokens=True):
        return ''.join(chr(int(i)) for i in ids if not (skip_special_tokens and int(i) in (0,EOS)))


class FakeClock:
    def __init__(self):self.t=0.0
    def __call__(self):return self.t


class MockCausalLM:
    """Emits a scripted answer token by token, then trailing junk the stop rule must cut.

    `slow_calls` makes chosen calls run past the per-call limit and emit a fragment.
    """
    device='cpu'
    def __init__(self,adapter_policies,tokenizer,clock=None,slow_calls=(),junk='\nTask: continue',step_seconds=0.25):
        self.script=ScriptedBackend(adapter_policies);self.tok=tokenizer
        self.clock=clock;self.slow=set(slow_calls);self.junk=junk;self.step_seconds=step_seconds
        self.calls=0;self.active_adapter=None
    def set_adapter(self,name):
        self.script.select(name);self.active_adapter=name
    def generate(self,input_ids,attention_mask,max_new_tokens,stopping_criteria,**kw):
        import torch
        if 'past_key_values' in kw:raise AssertionError('context carried between calls')
        prompt=self.tok.decode(input_ids[0])
        target=self.script.generate(prompt).text+self.junk
        slow=self.calls in self.slow;self.calls+=1
        if slow:target=target[:5]
        seq=input_ids
        for ch in target[:max_new_tokens]:
            seq=torch.cat([seq,torch.tensor([[ord(ch)]])],dim=1)
            if self.clock is not None:self.clock.t+=self.step_seconds
            if slow and self.clock is not None:self.clock.t+=1000
            if bool(torch.as_tensor(stopping_criteria(seq,None)).all()):break
        return seq


def mock_backend(adapter_policies,clock=None,per_call_seconds=60.0,**kw):
    tok=CharTokenizer();clock=clock or FakeClock()
    model=MockCausalLM(adapter_policies,tok,clock,**kw)
    adapters={k:f'mock://{k}' for k in adapter_policies}
    b=TransformersPeftBackend(model,tok,adapters,per_call_seconds=per_call_seconds,
                              provenance={'mock_model':True,'adapter_policies':dict(adapter_policies)},clock=clock)
    b.evidence_class='MOCK_MODEL_SYNTHETIC'
    return b


def _sha(p):return hashlib.sha256(Path(p).read_bytes().replace(b'\r\n',b'\n')).hexdigest()


def cpu_demo(out,source_revision=None):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    plan=build_plan(['S1','O1'],'calibration',seed=41)
    write_json(out/'plan.json',plan)
    runs={'scripted_honest_vs_conservative':ScriptedBackend({'S1':'honest','O1':'conservative'}),
          'mock_model_conservative_vs_honest':mock_backend({'S1':'conservative','O1':'honest'})}
    summary={}
    for name,backend in runs.items():
        d=out/name
        for f in ('rollouts.jsonl','rollouts.jsonl.xz','plan.json','run_manifest.json','score.json'):
            if (d/f).exists():(d/f).unlink()
        run_campaign(plan,backend,d,source_revision=source_revision)
        s=score_run(d)
        (d/'rollouts.jsonl.xz').write_bytes(lzma.compress((d/'rollouts.jsonl').read_bytes(),preset=9))
        pol=backend.describe().get('arm_policies') or backend.describe()['adapter_policies']
        arms={a:{'policy':pol[a],'J_minus':s['per_arm'][a]['decision']['J_minus'],
                 'TPR':s['per_arm'][a]['decision']['TPR'],'FPR':s['per_arm'][a]['decision']['FPR'],
                 'reporting_accuracy':s['per_arm'][a]['reporting']['accurate_rate_bounds'],
                 'malformed':s['per_arm'][a]['action_legality']['malformed'],
                 'unavailable_selected':s['per_arm'][a]['action_legality']['unavailable_selected'],
                 'environment_invalid':s['per_arm'][a]['action_legality']['environment_invalid']} for a in plan['params']['arms']}
        for a,x in arms.items():
            want={'honest':'1','conservative':'0'}[x['policy']]
            if x['J_minus']!=want or x['reporting_accuracy']!=['1','1'] or x['malformed'] or x['environment_invalid']:
                raise AssertionError(f'{name}/{a}: synthetic policy did not reach its analytic score')
        diff=s['paired']['O1_minus_S1']['J_minus_blocks']['mean_difference']
        expected=str(F(arms['O1']['J_minus'])-F(arms['S1']['J_minus']))
        if diff!=expected:raise AssertionError('paired J_minus difference wrong')
        summary[name]={'evidence_class':s['evidence_class'],'claim':s['claim'],'arms':arms,
                       'paired_J_minus_O1_minus_S1':diff,
                       'paired_reporting_O1_minus_S1':s['paired']['O1_minus_S1']['reporting_accuracy_blocks']['mean_difference'],
                       'records':s['records'],'generations':s['generations'],'status_counts':s['status_counts'],
                       'sha256':{f:_sha(d/f) for f in ('rollouts.jsonl','run_manifest.json','score.json')}}
    receipt={'status':'CPU_RUNNER_DEMO_VERIFIED','plan_sha256':plan['plan_sha256'],
             'plan_file_sha256':_sha(out/'plan.json'),'blocks':len(plan['blocks']),
             'arm_position_counts':plan['arm_position_counts'],'runs':summary,
             'source_sha256':source_hashes(),'source_revision':source_revision,
             'gpu_jobs':0,'paid_model_calls':0,'final_test_access':False,'weights_loaded':False,
             'not_a_model_result':True}
    write_json(out/'cpu_demo_receipt.json',receipt)
    return receipt
