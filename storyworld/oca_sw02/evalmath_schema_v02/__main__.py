"""Run `python -m storyworld.oca_sw02.evalmath_schema_v02 --help`."""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from .protocol import build_plan,validate_plan,save_json
from .runtime import run_campaign, ScriptedBackend, HFBackend
from .scoring import score_campaign
from .verify import main as verify_cpu


def main(argv=None):
    parser=argparse.ArgumentParser(description='OCA-SW-02R reporting schema equating v0.2')
    subs=parser.add_subparsers(dest='cmd',required=True)
    q=subs.add_parser('verify-cpu');q.add_argument('--out',type=Path)
    q=subs.add_parser('plan');q.add_argument('--out',type=Path,required=True)
    q=subs.add_parser('score');q.add_argument('--run',type=Path,required=True)
    for mode in ('scripted','infer'):
        q=subs.add_parser(mode);q.add_argument('--out',type=Path,required=True)
        q.add_argument('--max-seconds',type=int,default=900)
        if mode=='scripted':
            q.add_argument('--S1',choices=('truthful','legacy_choice_zero','default_zero','incentive','refuse'),required=True)
            q.add_argument('--O1',choices=('truthful','legacy_choice_zero','default_zero','incentive','refuse'),required=True)
        else:
            q.add_argument('--base',type=Path,required=True)
            q.add_argument('--adapter-s1',type=Path,required=True)
            q.add_argument('--adapter-o1',type=Path,required=True)
            q.add_argument('--approved',action='store_true')
            q.add_argument('--per-call-seconds',type=float,default=30.0)
            q.add_argument('--source-revision')
    args=parser.parse_args(argv)
    if args.cmd=='verify-cpu':
        result=verify_cpu(args.out)
        print(json.dumps({'status':result['status'],'tests_passed':result['tests_passed'],
                          'plan_sha256':result['plan_sha256'],'gpu_jobs':0},indent=2));return
    plan=build_plan();validate_plan(plan)
    frozen=json.loads((Path(__file__).resolve().parent/'results'/'frozen_plan.json').read_text(encoding='utf-8'))
    if frozen['version']!=plan['version'] or frozen['plan_sha256']!=plan['sha256']:
        raise SystemExit('frozen plan does not match this source; refusing execution')
    if args.cmd=='plan':save_json(args.out,plan);print(plan['sha256']);return
    if args.cmd=='score':
        r=score_campaign(args.run)
        print(json.dumps({'status':r['status'],'claim':r['claim'],'paired':r['paired_differences']},indent=2));return
    if not 1<=args.max_seconds<=3600:parser.error('invalid runtime bound')
    if args.cmd=='scripted':backend=ScriptedBackend({'S1':args.S1,'O1':args.O1})
    else:
        if not args.approved:parser.error('paid model inference requires explicit prior budget authorization and --approved')
        if not 1<=args.per_call_seconds<=120:parser.error('invalid per-call bound')
        backend=HFBackend.load(args.base,{'S1':args.adapter_s1,'O1':args.adapter_o1},
                               per_call_seconds=args.per_call_seconds)
    manifest=run_campaign(plan,backend,args.out,max_seconds=args.max_seconds,
                          source_revision=getattr(args,'source_revision',None))
    score=score_campaign(args.out)
    print(json.dumps({'status':'COMPLETE','manifest_status':manifest['status_counts'],
                      'paired_differences':score['paired_differences'],'gpu_jobs':manifest['gpu_jobs']},indent=2))

if __name__=='__main__':main()
