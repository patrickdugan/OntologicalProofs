"""Execute a frozen plan: every block, every arm, every unit, in plan order.

The runner has no access to scores. Timeouts and infrastructure failures end a
unit as unknown; once the campaign deadline passes, all remaining assigned
units are written as `not_executed`, so the record stays complete.
"""
from __future__ import annotations
import json
import platform
import subprocess
import time
from pathlib import Path
from ..core import World, write_json
from .plan import RUNNER_VERSION, validate_plan, case_from_dict, incident_from_dict
from .prompts import decision_prompt, reporting_prompt, sha, try_parse
from .backends import BackendFailure
from .provenance import source_hashes

STATUSES=('completed','timeout','infrastructure_failure','not_executed')


def _generation(step,prompt,g,lane):
    parsed,error=try_parse(lane,g.text)
    return {'step':step,'prompt':prompt,'prompt_sha256':sha(prompt),'raw':g.text,
            'parsed':parsed,'parse_error':error,**{k:v for k,v in g.to_dict().items() if k!='text'}}


def run_decision(unit,backend,expired):
    w=World(case_from_dict(unit['case']))
    gens=[];status='completed';reason=None
    while not w.done:
        prompt=decision_prompt(w.observation())
        if expired():status,reason='not_executed' if not gens else 'timeout','campaign_deadline';w.timeout();break
        try:g=backend.generate(prompt,'decision')
        except TimeoutError as exc:status,reason='timeout',str(exc) or 'timeout';w.timeout();break
        except BackendFailure as exc:status,reason='infrastructure_failure',str(exc);w.timeout();break
        gens.append(_generation(w.state.steps+1,prompt,g,'decision'))
        if g.stop=='time_limit' and gens[-1]['parsed'] is None:
            # A cut-off generation is unknown, not a model-chosen invalid action.
            status,reason='timeout','per_call_time_limit';w.timeout();break
        w.step(g.text)
    return {'status':status,'reason':reason,'generations':gens,'world_receipt':w.receipt()}


def run_reporting(unit,backend,expired):
    inc=incident_from_dict(unit['incident'])
    prompt=reporting_prompt(inc,unit['context'])
    if expired():return {'status':'not_executed','reason':'campaign_deadline','prompt_sha256':sha(prompt),'generations':[]}
    try:g=backend.generate(prompt,'reporting')
    except TimeoutError as exc:return {'status':'timeout','reason':str(exc) or 'timeout','prompt_sha256':sha(prompt),'generations':[]}
    except BackendFailure as exc:return {'status':'infrastructure_failure','reason':str(exc),'prompt_sha256':sha(prompt),'generations':[]}
    gen=_generation(1,prompt,g,'reporting')
    status,reason=('timeout','per_call_time_limit') if g.stop=='time_limit' and gen['parsed'] is None else ('completed',None)
    return {'status':status,'reason':reason,'prompt_sha256':sha(prompt),'generations':[gen]}


def git_revision(repo):
    try:
        r=subprocess.run(['git','rev-parse','HEAD'],cwd=repo,capture_output=True,text=True,timeout=10)
        return r.stdout.strip() if r.returncode==0 else None
    except (OSError,subprocess.SubprocessError):return None


def run_campaign(plan,backend,out,max_seconds=None,source_revision=None,clock=time.monotonic,
                 skip=None):
    """`skip(block,arm,records)` exists only so tests can build gated mutants."""
    validate_plan(plan)
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    if (out/'rollouts.jsonl').exists():raise FileExistsError('run directory already holds rollouts')
    write_json(out/'plan.json',plan)
    start=clock();deadline=None if max_seconds is None else start+max_seconds
    expired=lambda:deadline is not None and clock()>=deadline
    seq=0;counts={s:0 for s in STATUSES};records=[]
    with (out/'rollouts.jsonl').open('w',encoding='utf-8',newline='\n') as f:
        for block in plan['blocks']:
            units={u['unit_id']:u for u in block['units']}
            for position,arm in enumerate(block['arm_order']):
                if skip and skip(block,arm,records):continue
                backend.select(arm)
                for uid in block['unit_order']:
                    unit=units[uid]
                    body=(run_decision if unit['lane']=='decision' else run_reporting)(unit,backend,expired)
                    rec={'runner_version':RUNNER_VERSION,'plan_sha256':plan['plan_sha256'],'sequence':seq,
                         'block_index':block['block_index'],'motif_id':block['motif_id'],'arm':arm,
                         'arm_position':position,'unit_id':uid,'lane':unit['lane'],**body}
                    f.write(json.dumps(rec,sort_keys=True,ensure_ascii=True)+'\n');f.flush()
                    records.append({k:rec[k] for k in ('block_index','arm','unit_id','lane','status')})
                    counts[rec['status']]+=1;seq+=1
    elapsed=clock()-start
    repo=Path(__file__).resolve().parents[3]
    manifest={'runner_version':RUNNER_VERSION,'plan_sha256':plan['plan_sha256'],
              'backend':backend.describe(),'evidence_class':backend.evidence_class,
              'source_revision':source_revision or git_revision(repo),'source_sha256':source_hashes(),
              'records':seq,'status_counts':counts,'max_seconds':max_seconds,'elapsed_seconds':round(elapsed,3),
              'deadline_reached':bool(expired()) or counts['not_executed']>0,
              'python':platform.python_version(),'platform':platform.system(),
              'peak_cuda_bytes':backend.peak_memory() if hasattr(backend,'peak_memory') else None,
              'gpu_jobs':int(bool(backend.describe().get('gpu'))),
              # Hardware billing happens outside this process; only a CPU fixture can certify zero.
              'paid_model_calls':0 if backend.evidence_class!='MODEL_INFERENCE' else None,
              'final_test_access':False}
    write_json(out/'run_manifest.json',manifest)
    return manifest
