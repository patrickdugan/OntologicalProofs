"""Schema-v0.2 CPU scripted runner and optional local PEFT inference.

No model is loaded by importing this package. A GPU run is an explicit action.
The runner cannot access scores or modify a plan based on model output.
"""
from __future__ import annotations
from dataclasses import dataclass,asdict
from pathlib import Path
import json
import time
import platform
import subprocess
from fractions import Fraction as F
from .protocol import REPORTS, VERSION, canon, options, parse, prompt, source_hashes, validate_plan, save_json


@dataclass
class Response:
    text: str
    stop: str = 'parsed'
    prompt_tokens: int | None = None
    new_tokens: int | None = None
    seconds: float = 0.0


class InfraError(RuntimeError):pass


def public_from_prompt(p):
    if '\nObservation:\n' not in p or not p.endswith('\nReport JSON:\n'):
        raise ValueError('unrecognized reporting prompt')
    return json.loads(p.split('\nObservation:\n',1)[1].removesuffix('\nReport JSON:\n'))


class ScriptedBackend:
    evidence_class='SYNTHETIC_SCRIPTED_POLICY'
    def __init__(self, policies):
        if not policies or any(v not in ('truthful','legacy_choice_zero','default_zero','incentive','refuse') for v in policies.values()):
            raise ValueError('bad scripted policies')
        self.policies=dict(policies);self.active=None
    def select(self,arm):
        if arm not in self.policies:raise ValueError('missing scripted arm')
        self.active=arm
    def generate(self,p,unit):
        # The fixture deliberately reasons only over the serialized public prompt.
        view=public_from_prompt(p)
        schema=unit['schema'];policy=self.policies[self.active]
        labels=view['choices']
        if policy=='legacy_choice_zero':return Response('{"choice":0}','scripted')
        if policy=='default_zero':
            return Response('{"choice":0}' if schema=='choice' else '{"report":"change"}','scripted')
        if policy=='refuse':content='stop'
        else:
            signed=view['evidence']['signed_execution']
            content='change' if 'transferred' in signed else 'retain'
            if policy=='incentive' and 'violated' in view['evidence']['compliance_finding'] and F(view['evidence']['audit_probability'])<F(1,2):
                content='retain' if content=='change' else 'change'
        tok=next(x['token'] for x in labels if ((content=='change' and 'transfer was executed' in x['meaning'])
                    or (content=='retain' and 'allocation was retained' in x['meaning'])
                    or (content=='stop' and 'File no report' in x['meaning'])))
        obj={'report':tok} if schema=='named' else {'choice':tok}
        return Response(canon(obj),'scripted')
    def describe(self):return {'kind':'scripted','policies':self.policies,'gpu':False}


class HFBackend:
    evidence_class='MODEL_INFERENCE'
    def __init__(self,loaded,per_call_seconds=30.0):
        self.loaded=loaded;self.model=loaded.model;self.tok=loaded.tok
        self.active=None;self.adapters=loaded.adapters;self.per_call_seconds=per_call_seconds
    @classmethod
    def load(cls,base,adapters,per_call_seconds=30.0,hash_weights=False):
        from ..evalmath_runner.backends import TransformersPeftBackend
        loaded=TransformersPeftBackend.load(base,adapters,per_call_seconds=per_call_seconds,hash_weights=hash_weights)
        return cls(loaded,per_call_seconds)
    def select(self,arm):
        if arm not in self.adapters:raise ValueError('unknown arm')
        self.loaded.select(arm);self.active=arm
    def generate(self,p,unit):
        import torch
        from transformers import StoppingCriteriaList,MaxTimeCriteria
        tok=self.tok;model=self.model
        enc=tok(p,return_tensors='pt',add_special_tokens=False)
        n=int(enc['input_ids'].shape[1])
        if n>4096:raise InfraError('prompt context exceeds 4096 tokens')
        ids=enc['input_ids'].to(model.device);mask=enc['attention_mask'].to(model.device)
        class StrictStop:
            def __call__(self,input_ids,scores,**kw):
                raw=tok.decode(input_ids[0,n:],skip_special_tokens=True)
                try:parse(unit,raw);return True
                except (ValueError,TypeError,KeyError):return False
        stopping=[StrictStop()]
        if self.per_call_seconds:stopping.append(MaxTimeCriteria(self.per_call_seconds))
        start=time.monotonic()
        try:
            with torch.inference_mode():
                out=model.generate(input_ids=ids,attention_mask=mask,do_sample=False,
                                   max_new_tokens=48,pad_token_id=tok.pad_token_id,
                                   stopping_criteria=StoppingCriteriaList(stopping))
        except (RuntimeError,MemoryError) as exc:raise InfraError(str(exc)) from exc
        elapsed=time.monotonic()-start
        generated=out[0,n:];raw=tok.decode(generated,skip_special_tokens=True)
        try:parse(unit,raw);stop='parsed'
        except (ValueError,TypeError,KeyError):
            stop='time_limit' if self.per_call_seconds and elapsed>=self.per_call_seconds else 'max_new_tokens'
        return Response(raw,stop,n,int(len(generated)),elapsed)
    def describe(self):return {'kind':'transformers_peft','gpu':True,'adapters':sorted(self.adapters),
                               'base':self.loaded.describe(),'per_call_seconds':self.per_call_seconds}
    def peak_memory(self):return self.loaded.peak_memory()


def git_revision():
    try:
        root=Path(__file__).resolve().parents[3]
        r=subprocess.run(['git','rev-parse','HEAD'],cwd=root,capture_output=True,text=True,timeout=5)
        return r.stdout.strip() if r.returncode==0 else None
    except (OSError,subprocess.SubprocessError):return None


def run_campaign(plan,backend,out,max_seconds=None,source_revision=None,clock=time.monotonic):
    validate_plan(plan)
    out=Path(out)
    if out.exists():raise FileExistsError('output path must be new and empty')
    out.mkdir(parents=True)
    save_json(out/'plan.json',plan)
    records=0;counts={'completed':0,'timeout':0,'infrastructure_failure':0,'not_executed':0}
    start=clock();deadline=start+max_seconds if max_seconds is not None else None
    with (out/'rollouts.jsonl').open('w',encoding='utf-8',newline='\n') as f:
        for b in plan['blocks']:
            by_id={u['unit_id']:u for u in b['units']}
            for arm in b['arm_order']:
                backend.select(arm)
                for uid in b['unit_order']:
                    u=by_id[uid];p=prompt(u)
                    rec={'sequence':records,'motif_id':b['motif_id'],'block_index':b['block_index'],
                         'arm':arm,'unit_id':uid,'schema':u['schema'],'shift':u['shift'],
                         'prompt':p,'prompt_sha256':hashlib_sha(p),'status':'completed','raw':None,
                         'stop':None,'reason':None,'prompt_tokens':None,'new_tokens':None,'seconds':None}
                    if deadline is not None and clock()>=deadline:
                        rec.update(status='not_executed',reason='campaign_deadline')
                    else:
                        try:
                            g=backend.generate(p,u)
                            rec.update(raw=g.text,stop=g.stop,prompt_tokens=g.prompt_tokens,
                                       new_tokens=g.new_tokens,seconds=g.seconds)
                            if g.stop=='time_limit':
                                try:parse(u,g.text)
                                except (ValueError,TypeError,KeyError):rec.update(status='timeout',reason='per_call_limit')
                        except TimeoutError as exc:rec.update(status='timeout',reason=str(exc) or 'timeout')
                        except InfraError as exc:rec.update(status='infrastructure_failure',reason=str(exc))
                    f.write(json.dumps(rec,sort_keys=True,ensure_ascii=True)+'\n')
                    counts[rec['status']]+=1;records+=1
    elapsed=clock()-start
    manifest={'version':VERSION,'plan_sha256':plan['sha256'],'source_sha256':source_hashes(),
              'source_revision':source_revision or git_revision(),'backend':backend.describe(),
              'evidence_class':backend.evidence_class,'records':records,'status_counts':counts,
              'gpu_jobs':int(backend.evidence_class=='MODEL_INFERENCE'),
              'peak_cuda_bytes':backend.peak_memory() if hasattr(backend,'peak_memory') else None,
              'wall_seconds':round(elapsed,3),'max_seconds':max_seconds,
              'final_test_access':False,'python':platform.python_version()}
    save_json(out/'run_manifest.json',manifest)
    return manifest


def hashlib_sha(s):
    import hashlib
    return hashlib.sha256(s.encode('utf-8')).hexdigest()
