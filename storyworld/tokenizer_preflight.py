"""CPU-only, offline preflight using the exact tokenizer files from a retained checkpoint.

Run:
 python -m storyworld.tokenizer_preflight --checkpoint /mounted/checkpoint \
   --revision 1d4bf0f2ff6012fd82039f2fa52739d0dd7c60c0 \
   --out /tmp/oca-tokenizer-preflight.json

Requires a locally installed Transformers version supporting the tokenizer.
Never loads weights, accesses model endpoints, or allocates CUDA.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
from .train import matched_schedules
from .oca import write_json

PINNED_REVISION='1d4bf0f2ff6012fd82039f2fa52739d0dd7c60c0'
SEEDS=(11,29,47)

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inspect(tokenizer, revision=PINNED_REVISION, steps=50, context=2048):
    runs=[]
    for seed in SEEDS:
        schedules, meta=matched_schedules(tokenizer,seed,steps,context)
        arms={}
        for arm,exs in schedules.items():
            lengths=[len(ids) for ids,_ in exs]
            supervised=[sum(x!=-100 for x in labs) for _,labs in exs]
            arms[arm]={'steps':len(exs),'actual_tokens':sum(lengths),
                       'supervised_tokens':sum(supervised),
                       'max_example_length':max(lengths),'lengths_sha256':hashlib.sha256(
                           json.dumps(lengths).encode()).hexdigest()}
            assert all(len(a)==len(b) for a,b in exs)
        if arms['S1']['actual_tokens'] != arms['O1']['actual_tokens']:
            raise AssertionError('paired input tokens differ')
        if arms['S1']['actual_tokens'] > 200000:
            raise ValueError('paired schedule exceeds training cap')
        runs.append({'seed':seed,'arms':arms,'schedule':meta,
                     'paired_lengths_equal':all(len(a[0])==len(b[0])
                         for a,b in zip(schedules['S1'],schedules['O1']))})
    return {'status':'CPU_TOKENIZER_PREFLIGHT_PASS','checkpoint_revision':revision,
            'steps':steps,'context':context,'seeds':list(SEEDS),'runs':runs,
            'caveat':'EOS equalization changes supervised targets; matching input token counts alone does not make training treatments causally identical.'}

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--checkpoint',type=Path,required=True)
    p.add_argument('--revision',required=True)
    p.add_argument('--out',type=Path,required=True)
    p.add_argument('--steps',type=int,default=50)
    args=p.parse_args()
    if args.revision!=PINNED_REVISION: p.error('pinned revision mismatch')
    if not args.checkpoint.is_dir(): p.error('retained checkpoint directory missing')
    if not (args.checkpoint/'tokenizer_config.json').is_file():
        p.error('tokenizer_config.json missing')
    if not (args.checkpoint/'tokenizer.json').is_file():
        p.error('tokenizer.json missing')
    os.environ['HF_HUB_OFFLINE']='1'
    os.environ['TRANSFORMERS_OFFLINE']='1'
    from transformers import AutoTokenizer
    tokenizer=AutoTokenizer.from_pretrained(str(args.checkpoint),local_files_only=True,
                                             trust_remote_code=False)
    if tokenizer.eos_token_id is None: p.error('EOS token ID missing')
    report=inspect(tokenizer,args.revision,args.steps)
    report['checkpoint_tokenizer_sha256']={k:sha(args.checkpoint/k)
          for k in ('tokenizer_config.json','tokenizer.json')}
    report['tokenizer_class']=type(tokenizer).__name__
    write_json(args.out,report)
    print(json.dumps({'status':report['status'],'output':str(args.out),
                      'runs':len(report['runs'])},indent=2))
if __name__=='__main__':main()
