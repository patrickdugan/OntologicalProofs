#!/usr/bin/env bash
# OCA-SW-02R development-only S1/O1 pilot. Hard external GPU wall limit
# covers model loading, adapter attachment, generation, and scoring.
set -euo pipefail
START_SECONDS=$(date +%s)
if [[ $# -ne 4 ]]; then
  printf 'Usage: %s BASE_MODEL_DIR S1_ADAPTER_DIR O1_ADAPTER_DIR NEW_OUTPUT_DIR\n' "$0" >&2
  exit 64
fi
BASE=$1; S1=$2; O1=$3; OUT=$4
for path in "$BASE" "$S1" "$O1"; do
  if [[ ! -d "$path" ]]; then printf 'Missing local model directory: %s\n' "$path" >&2; exit 66; fi
done
if [[ -e "$OUT" ]]; then printf 'Output already exists: %s\n' "$OUT" >&2; exit 73; fi
if ! command -v timeout >/dev/null 2>&1; then
  printf 'GNU timeout is required to enforce the all-in 20-minute cap.\n' >&2; exit 69
fi
ROOT=$(cd "$(dirname "${BASH_SOURCE[0]}")/../../../.." && pwd)
cd "$ROOT"
export HF_HUB_OFFLINE=1 TRANSFORMERS_OFFLINE=1 HF_DATASETS_OFFLINE=1
# Scheduler must allocate and bill for only one H100.
export CUDA_VISIBLE_DEVICES="${CUDA_VISIBLE_DEVICES:-0}"
export PYTHONUNBUFFERED=1
PLAN=storyworld/oca_sw02/evalmath_runner/results/plan.json
python - "$PLAN" <<'PY'
import json,sys
import torch
from storyworld.oca_sw02.evalmath_runner.plan import validate_plan,regenerate_and_compare,case_from_dict
from storyworld.oca_sw02.evalmath_runner.prompts import decision_prompt,observation_from_prompt,reporting_prompt
from storyworld.oca_sw02.evalmath_runner.plan import incident_from_dict
from storyworld.oca_sw02.core import World,oracle_dnf
plan=json.load(open(sys.argv[1],encoding='utf-8'))
validate_plan(plan);regenerate_and_compare(plan)
assert plan['params']['arms']==['S1','O1']
assert plan['params']['split']=='calibration'
assert len(plan['blocks'])==16
assert plan['arm_position_counts']=={'S1':[8,8],'O1':[8,8]}
decisions=reports=0
for block in plan['blocks']:
    for unit in block['units']:
        if unit['lane']=='decision':
            c=case_from_dict(unit['case']);obs=World(c).observation()
            lane,view=observation_from_prompt(decision_prompt(obs))
            assert lane=='decision' and c.hidden is None
            assert all(v in ('authenticated: yes','authenticated: no') for v in view['authenticated_records'].values())
            assert oracle_dnf(c.family,c.facts)==unit['authorized']
            assert any(a['description']=='execute the proposed transfer' and a['available'] for a in view['actions'])
            assert any(a['description']=='retain the current allocation' and a['available'] for a in view['actions'])
            decisions+=1
        else:
            inc=incident_from_dict(unit['incident'])
            prompt=reporting_prompt(inc,unit['context'])
            lane,view=observation_from_prompt(prompt)
            assert lane=='reporting' and 'audit_draw' not in view
            assert view['audit_probability'] in ('1/10','9/10')
            reports+=1
assert (decisions,reports)==(128,64)
print(json.dumps({'status':'CPU_PREFLIGHT_PASS','plan_sha256':plan['plan_sha256'],
                  'motifs':16,'decision_units_per_arm':decisions,
                  'reporting_units_per_arm':reports,'gpu_jobs':0},sort_keys=True))
if not torch.cuda.is_available():raise SystemExit('No CUDA GPU; refusing to start paid model inference')
if torch.cuda.device_count()!=1:raise SystemExit('Expected exactly one visible CUDA GPU')
name=torch.cuda.get_device_name(0)
free,total=torch.cuda.mem_get_info(0)
if 'H100' not in name or total<70*1024**3 or free<65*1024**3:
    raise SystemExit(f'Need one mostly free 80GB H100; found {name}, total={total}, free={free}')
print(f'GPU preflight passed: {name}, free GiB={free/1024**3:.1f}')
PY
# Start-to-finish limit: TERM by 1190 seconds and KILL by 1200 seconds,
# including CPU/GPU preflight, HF/PEFT load, evaluation and scoring.
# Runner itself stops generation after 900 seconds to allow scoring headroom.
remaining=$((1190 - ($(date +%s) - START_SECONDS)))
if [[ $remaining -le 0 ]]; then printf '20-minute budget exhausted during preflight.\n' >&2; exit 124; fi
set +e
timeout --signal=TERM --kill-after=10s "${remaining}s" \
  python -m storyworld.oca_sw02.evalmath_runner infer \
  --approved --plan "$PLAN" --base "$BASE" \
  --adapter "S1=$S1" --adapter "O1=$O1" \
  --out "$OUT" --max-seconds 900 --per-call-seconds 30 \
  --source-revision "$(git rev-parse HEAD)"
status=$?
set -e
if [[ "$status" -eq 124 || "$status" -eq 137 ]]; then
  printf 'Hard 20-minute wall limit reached. Preserve partial rollouts for forensic recovery; scoring may be unavailable.\n' >&2
fi
exit "$status"
