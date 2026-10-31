"""Four-device independent-run planner. Does not provision or purchase compute."""
from __future__ import annotations
import argparse
import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path
from .oca import write_json


def plan():
    jobs=[{'arm':a,'seed':s,'device':i%4,'wave':i//4,'steps':50,'seconds':1200} for i,(s,a) in enumerate((s,a) for s in (11,29,47) for a in ('S1','O1'))]
    return {'hardware_request':'4 x NVIDIA A100, independent single-GPU LoRA runs',
       'jobs':jobs,'max_waves':2,'max_node_seconds':3000,'max_job_seconds':1200,
       'funds_authorized':False,'price':'provider quote required','purpose':'pipeline smoke, not final-test evidence'}


def validate_approval(a):
    required=('approved_by','max_usd','node_hourly_usd','quote_timestamp','checkpoint_revision')
    if any(k not in a for k in required):raise ValueError('approval missing required fields')
    if not a['approved_by'] or not a['checkpoint_revision'] or not a['quote_timestamp']:raise ValueError('empty approval identity/revision')
    for k in ('max_usd','node_hourly_usd'):
        if isinstance(a[k],bool) or not isinstance(a[k],(int,float)) or not 0<a[k]<1e6:raise ValueError('invalid price/cap')
    if a['max_usd'] < a['node_hourly_usd']*plan()['max_node_seconds']/3600:raise ValueError('cap below worst-case quoted node time')


def launch(model:Path,out:Path,approval:dict):
    validate_approval(approval)
    import torch
    if torch.cuda.device_count()!=4:raise RuntimeError('exactly four visible devices required')
    if any('A100' not in torch.cuda.get_device_name(i) for i in range(4)):raise RuntimeError('hardware differs from requested A100 plan')
    if out.exists():raise ValueError('fresh output directory required')
    out.mkdir(parents=True);write_json(out/'approval.json',approval);start=time.monotonic();runs=[]
    try:
        for wave in (0,1):
            active=[]
            for j in (x for x in plan()['jobs'] if x['wave']==wave):
                dest=out/f"{j['arm']}-seed{j['seed']}"
                cmd=[sys.executable,'-m','storyworld.train','--approved','--model',str(model),'--arm',j['arm'],'--seed',str(j['seed']),
                     '--steps',str(j['steps']),'--seconds',str(j['seconds']),'--out',str(dest)]
                env=dict(os.environ,CUDA_VISIBLE_DEVICES=str(j['device']),HF_HUB_OFFLINE='1',TRANSFORMERS_OFFLINE='1',OMP_NUM_THREADS='2')
                log=open(out/f"{j['arm']}-{j['seed']}.log",'w')
                process=subprocess.Popen(cmd,env=env,stdout=log,stderr=subprocess.STDOUT,start_new_session=True)
                active.append((process,log,j,time.monotonic()))
            while any(p.poll() is None for p,_,_,_ in active):
                for p,log,j,t0 in active:
                    if p.poll() is None and (time.monotonic()-t0>j['seconds']+120 or time.monotonic()-start>plan()['max_node_seconds']):
                        os.killpg(p.pid,signal.SIGTERM)
                        try:p.wait(timeout=10)
                        except subprocess.TimeoutExpired:os.killpg(p.pid,signal.SIGKILL);p.wait()
                time.sleep(.25)
            for p,log,j,t0 in active:
                log.close()
                rp=out/f"{j['arm']}-seed{j['seed']}"/'run.json'
                receipt=json.loads(rp.read_text()) if rp.is_file() else {}
                runs.append(dict(j,exit_code=p.returncode,wall_seconds=time.monotonic()-t0,status=receipt.get('status','MISSING_RECEIPT')))
            if any(r['exit_code']!=0 or r['status']!='SMOKE_COMPLETE' for r in runs):raise RuntimeError('failed smoke; stopping subsequent wave')
    finally:
        for item in locals().get('active',[]):
            p,log,_,_=item
            if p.poll() is None:os.killpg(p.pid,signal.SIGKILL);p.wait()
            if not log.closed:log.close()
        write_json(out/'cluster_receipt.json',{'runs':runs,'wall_seconds':time.monotonic()-start,
            'billing':'time-based estimate only; provider invoice authoritative','shutdown':'processes ended; owner must release rented node'})


def main():
    p=argparse.ArgumentParser();p.add_argument('--launch',action='store_true');p.add_argument('--model',type=Path)
    p.add_argument('--out',type=Path);p.add_argument('--approval',type=Path);a=p.parse_args()
    if not a.launch:print(json.dumps(plan(),indent=2));return
    if None in (a.model,a.out,a.approval):p.error('launch requires model, out and approval')
    launch(a.model,a.out,json.loads(a.approval.read_text()))

if __name__=='__main__':main()
