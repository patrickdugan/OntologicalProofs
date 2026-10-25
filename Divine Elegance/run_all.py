"""Run offline, synthetic checks. Exit nonzero if any claimed fixture fails."""
import subprocess,sys,hashlib,json,datetime
from pathlib import Path
ROOT=Path(__file__).resolve().parent
TASKS=[f'experiments.e{i:02d}_'+name for i,name in [
 (1,'salvation_models'),(2,'global_gluing'),(3,'nineteen'),
 (4,'constrained_elegance'),(5,'relevant_invariance'),(6,'defensive_action_gate')]]
status={}
for task in TASKS:
    p=subprocess.run([sys.executable,'-m',task],cwd=ROOT,capture_output=True,text=True)
    status[task]={'exit_code':p.returncode,'stderr':p.stderr[-1600:]}
    if p.returncode:
        print(task,p.stderr,file=sys.stderr)
        break
else:
    p=subprocess.run([sys.executable,'-m','unittest','discover','-s','tests','-v'],cwd=ROOT,
                     capture_output=True,text=True)
    status['unittest']={'exit_code':p.returncode,'stderr':p.stderr[-4000:]}
    print(p.stderr)
status['lean_compiler']={'status':'NOT_RUN','reason':'Lean compiler unavailable in this environment. Must run pinned lake build.'}
(ROOT/'artifacts'/'RUN_STATUS.json').write_text(json.dumps(status,indent=2)+'\n')
if any(x.get('exit_code',0)!=0 for x in status.values()): sys.exit(1)
print('Synthetic experiments and unit tests PASS; Lean kernel compilation still required.')
