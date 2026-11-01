"""OCA-SW-02R runner CLI.

  plan      freeze an assignment plan
  run       execute a plan with a scripted or local Transformers/PEFT backend
  score     write an independent score receipt for a run directory
  infer     plan (or load a plan), run retained adapters, and score, in one command
  cpu-demo  scripted honest/conservative and mock-model runs with receipts
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from .plan import build_plan, validate_plan, regenerate_and_compare
from .runner import run_campaign
from .scoring import score_run
from .backends import ScriptedBackend, TransformersPeftBackend


def pairs(values,flag):
    out={}
    for v in values or []:
        if '=' not in v:raise SystemExit(f'{flag} expects NAME=VALUE, got {v!r}')
        k,x=v.split('=',1)
        if k in out:raise SystemExit(f'duplicate {flag} for {k}')
        out[k]=x
    return out


def add_plan_args(p):
    p.add_argument('--split',choices=('train','calibration'),default='calibration')
    p.add_argument('--seed',type=int,default=41)
    p.add_argument('--motifs-per-family',type=int,default=1)
    p.add_argument('--themes',nargs='+')
    p.add_argument('--families',nargs='+',type=int)


def plan_from(a,arms):
    if getattr(a,'plan',None):
        plan=json.loads(Path(a.plan).read_text(encoding='utf-8'))
        validate_plan(plan);regenerate_and_compare(plan)
        if sorted(plan['params']['arms'])!=sorted(arms):raise SystemExit('plan arms differ from supplied arms')
        return plan
    return build_plan(arms,a.split,a.themes,a.families,a.motifs_per_family,a.seed)


def transformers_backend(a):
    adapters={k:Path(v) for k,v in pairs(a.adapter,'--adapter').items()}
    if len(adapters)<2:raise SystemExit('paired inference needs two or more --adapter NAME=PATH')
    if not a.approved:raise SystemExit('model inference requires an explicit separately approved budget and --approved')
    return TransformersPeftBackend.load(a.base,adapters,a.tokenizer,a.per_call_seconds,a.hash_weights),list(adapters)


def add_model_args(p):
    p.add_argument('--base',type=Path,required=True)
    p.add_argument('--adapter',action='append',required=True,help='NAME=PATH; NAME is the plan arm')
    p.add_argument('--tokenizer',type=Path)
    p.add_argument('--approved',action='store_true')
    p.add_argument('--per-call-seconds',type=float,default=60.0)
    p.add_argument('--hash-weights',action='store_true',help='hash every base weight shard before loading')


def main(argv=None):
    ap=argparse.ArgumentParser(prog='python -m storyworld.oca_sw02.evalmath_runner')
    sub=ap.add_subparsers(dest='cmd',required=True)
    p=sub.add_parser('plan');add_plan_args(p)
    p.add_argument('--arms',nargs='+',default=['S1','O1']);p.add_argument('--out',type=Path,required=True)
    r=sub.add_parser('run');r.add_argument('--plan',type=Path,required=True);r.add_argument('--out',type=Path,required=True)
    r.add_argument('--backend',choices=('scripted','transformers'),required=True)
    r.add_argument('--policy',action='append',help='scripted backend: ARM=POLICY')
    r.add_argument('--base',type=Path);r.add_argument('--adapter',action='append');r.add_argument('--tokenizer',type=Path)
    r.add_argument('--approved',action='store_true');r.add_argument('--per-call-seconds',type=float,default=60.0)
    r.add_argument('--hash-weights',action='store_true')
    r.add_argument('--max-seconds',type=int,default=3600);r.add_argument('--source-revision')
    s=sub.add_parser('score');s.add_argument('--run',type=Path,required=True)
    i=sub.add_parser('infer');add_plan_args(i);add_model_args(i)
    i.add_argument('--plan',type=Path,help='frozen plan.json; overrides the plan arguments')
    i.add_argument('--out',type=Path,required=True);i.add_argument('--max-seconds',type=int,default=3600)
    i.add_argument('--source-revision')
    d=sub.add_parser('cpu-demo');d.add_argument('--out',type=Path,required=True)
    d.add_argument('--source-revision')
    a=ap.parse_args(argv)
    if a.cmd=='plan':
        plan=build_plan(a.arms,a.split,a.themes,a.families,a.motifs_per_family,a.seed)
        a.out.mkdir(parents=True,exist_ok=True)
        (a.out/'plan.json').write_text(json.dumps(plan,sort_keys=True,indent=2)+'\n',encoding='utf-8')
        print(json.dumps({'plan_sha256':plan['plan_sha256'],'blocks':len(plan['blocks']),
                          'arm_position_counts':plan['arm_position_counts']},indent=2));return
    if a.cmd=='score':
        out=score_run(a.run);print(json.dumps({k:out[k] for k in ('status','evidence_class','claim','status_counts')},indent=2));return
    if a.cmd=='cpu-demo':
        from .demo import cpu_demo
        print(json.dumps(cpu_demo(a.out,a.source_revision),indent=2));return
    if not 1<=a.max_seconds<=4*3600:ap.error('max-seconds out of bounds')
    if a.cmd=='run':
        plan=json.loads(a.plan.read_text(encoding='utf-8'));validate_plan(plan);regenerate_and_compare(plan)
        if a.backend=='scripted':
            backend=ScriptedBackend(pairs(a.policy,'--policy'))
        else:
            if a.base is None:ap.error('--base required')
            backend,_=transformers_backend(a)
    else:
        backend,arms=transformers_backend(a)
        plan=plan_from(a,arms)
    if sorted(plan['params']['arms'])!=sorted(getattr(backend,'policies',None) or backend.adapters):
        ap.error('backend arms differ from plan arms')
    manifest=run_campaign(plan,backend,a.out,a.max_seconds,a.source_revision)
    out=score_run(a.out)
    print(json.dumps({'manifest':{k:manifest[k] for k in ('plan_sha256','records','status_counts','elapsed_seconds','peak_cuda_bytes')},
                      'paired':{k:{'J_minus':v['J_minus_blocks']['mean_difference_bounds'],
                                   'reporting_accuracy':v['reporting_accuracy_blocks']['mean_difference_bounds']}
                                for k,v in out['paired'].items()}},indent=2))


if __name__=='__main__':main()
