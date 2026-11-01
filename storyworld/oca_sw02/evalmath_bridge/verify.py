"""Run CPU suites and regenerate source-hashed evidence without network or GPU."""
from __future__ import annotations
import argparse
import hashlib
import json
import platform
import re
import subprocess
import sys
from pathlib import Path
from .certificate import write_artifacts

REPO=Path(__file__).resolve().parents[3]
COMMANDS=(
 ['-m','unittest','discover','-s','storyworld/oca_sw02/evalmath_bridge/tests','-v'],
 ['-m','unittest','discover','-s','storyworld/tests','-p','test_sw02.py','-v'],
 ['-m','unittest','discover','-s','storyworld/tests','-p','test_sw02_premise.py','-v'],
)

def verify(out):
    out=Path(out);out.mkdir(parents=True,exist_ok=True)
    full_tests=[]
    if not (REPO/'storyworld/oca_sw02/worlds/masked_ledger.json').exists():
        cmd=[sys.executable,'-m','storyworld.oca_sw02.native','--out','storyworld/oca_sw02/worlds']
        native=subprocess.run(cmd,cwd=REPO,text=True,capture_output=True,timeout=150)
        if native.returncode:raise RuntimeError('native generation failed: '+native.stderr[-1200:])
    for parts in COMMANDS:
        proc=subprocess.run([sys.executable,*parts],cwd=REPO,text=True,capture_output=True,timeout=120)
        log=proc.stdout+'\n'+proc.stderr
        match=re.search(r'Ran (\d+) tests?',log)
        n=int(match.group(1)) if match else 0
        skip=re.search(r'OK \(skipped=(\d+)\)',log)
        skipped=int(skip.group(1)) if skip else 0
        if proc.returncode or 'FAILED (' in log or not match:
            raise RuntimeError(f'CPU suite failed: {parts}: '+log[-3000:])
        full_tests.append({'command':'python '+' '.join(parts),'exit_code':proc.returncode,
                           'tests_run':n,'skipped':skipped,'passed':n-skipped,
                           'log_sha256':hashlib.sha256(log.encode()).hexdigest()})
    files=write_artifacts(out)
    receipt={'status':'CPU_VERIFIED_WITH_SKIPS' if sum(x['skipped'] for x in full_tests) else 'CPU_VERIFIED',
             'python':platform.python_version(),'platform':platform.system(),
             'tests_run':sum(x['tests_run'] for x in full_tests),
             'tests_passed':sum(x['passed'] for x in full_tests),
             'tests_skipped':sum(x['skipped'] for x in full_tests),
             'tests_failed':0,'commands':full_tests,
             'output_sha256':{p:hashlib.sha256((out/p).read_bytes()).hexdigest() for p in files},
             'gpu_jobs':0,'paid_model_calls':0,'final_test_access':False,
             'evidence_status':'synthetic_and_exact_finite_only'}
    (out/'cpu_verification.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
    return receipt

def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True)
    args=p.parse_args();print(json.dumps(verify(args.out),indent=2))
if __name__=='__main__':main()
