"""Run every Storyworld/OCA CPU suite plus the runner suite, then regenerate the CPU demo receipts.

python -m storyworld.oca_sw02.evalmath_runner.verify --out storyworld/oca_sw02/evalmath_runner/results
"""
from __future__ import annotations
import argparse
import hashlib
import json
import platform
import re
import subprocess
import sys
from pathlib import Path
from .demo import cpu_demo
from .provenance import REPO, source_hashes

COMMANDS=(
 ['-m','unittest','discover','-s','storyworld/oca_sw02/evalmath_bridge/tests','-v'],
 ['-m','unittest','discover','-s','storyworld/tests','-p','test_*.py','-v'],
 ['-m','unittest','storyworld.oca_sw02.test_audit_traces','-v'],
 ['-m','unittest','discover','-s','storyworld/oca_sw02/evalmath_runner/tests','-v'],
)
WORLDS=(
 (REPO/'storyworld/worlds/common_spring.json',['-m','storyworld.build_world','build','--out','storyworld/worlds']),
 (REPO/'storyworld/oca_sw02/worlds/masked_ledger.json',['-m','storyworld.oca_sw02.native','--out','storyworld/oca_sw02/worlds']),
)


def run_suite(parts):
    proc=subprocess.run([sys.executable,*parts],cwd=REPO,text=True,capture_output=True,timeout=600)
    log=proc.stdout+'\n'+proc.stderr
    ran=re.search(r'Ran (\d+) tests?',log);skip=re.search(r'skipped=(\d+)',log)
    if proc.returncode or not ran:raise RuntimeError(f'CPU suite failed: {parts}: '+log[-3000:])
    n=int(ran.group(1));skipped=int(skip.group(1)) if skip else 0
    return {'command':'python '+' '.join(parts),'exit_code':proc.returncode,'tests_run':n,'skipped':skipped,
            'passed':n-skipped,'log_sha256':hashlib.sha256(log.encode()).hexdigest()}


def verify(out,source_revision=None):
    out=Path(out)
    for path,cmd in WORLDS:
        if not path.exists():
            p=subprocess.run([sys.executable,*cmd],cwd=REPO,text=True,capture_output=True,timeout=300)
            if p.returncode:raise RuntimeError('world generation failed: '+p.stderr[-1200:])
    demo=cpu_demo(out,source_revision)
    # The runner suite includes a rescore of the receipts written just above.
    suites=[run_suite(c) for c in COMMANDS]
    import importlib.util
    deps={m:bool(importlib.util.find_spec(m)) for m in ('gymnasium','torch','transformers','peft')}
    receipt={'status':'CPU_VERIFIED_WITH_SKIPS' if sum(x['skipped'] for x in suites) else 'CPU_VERIFIED',
             'python':platform.python_version(),'platform':platform.system(),'optional_dependencies':deps,
             'tests_run':sum(x['tests_run'] for x in suites),'tests_passed':sum(x['passed'] for x in suites),
             'tests_skipped':sum(x['skipped'] for x in suites),'tests_failed':0,'commands':suites,
             'demo_status':demo['status'],'plan_sha256':demo['plan_sha256'],
             'demo_receipt_sha256':hashlib.sha256((out/'cpu_demo_receipt.json').read_bytes().replace(b'\r\n',b'\n')).hexdigest(),
             'source_sha256':source_hashes(),'source_revision':source_revision,
             'gpu_jobs':0,'paid_model_calls':0,'final_test_access':False,'weights_loaded':False,
             'evidence_status':'synthetic_scripted_and_mock_model_only'}
    (out/'cpu_verification.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n',encoding='utf-8')
    return receipt


def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True);p.add_argument('--source-revision')
    a=p.parse_args();print(json.dumps(verify(a.out,a.source_revision),indent=2))
if __name__=='__main__':main()
