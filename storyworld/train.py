"""Offline HF/PEFT runner. No model is downloaded or loaded by import.
This is a bounded smoke runner. Full-pilot admission additionally needs matched
actual token budgets, a competence gate, and sealed final-test custody.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import random
import time
from pathlib import Path
from .oca import curriculum, digest, write_json


def encode_example(tokenizer,row,max_length):
    prompt='Task:\n'+row['prompt']+'\nAnswer:\n'
    p=tokenizer.encode(prompt,add_special_tokens=False)
    a=tokenizer.encode(row['answer'],add_special_tokens=False)+[tokenizer.eos_token_id]
    if not a or len(p)+len(a)>max_length: raise ValueError('example exceeds context; revise data explicitly')
    return p+a,[-100]*len(p)+a


def batch_tensors(examples,pad_id,device):
    import torch
    n=max(len(x[0]) for x in examples)
    return {'input_ids':torch.tensor([x[0]+[pad_id]*(n-len(x[0])) for x in examples],device=device),
      'attention_mask':torch.tensor([[1]*len(x[0])+[0]*(n-len(x[0])) for x in examples],device=device),
      'labels':torch.tensor([x[1]+[-100]*(n-len(x[1])) for x in examples],device=device)}


def source_manifest(model:Path):
    if not model.is_dir(): raise ValueError('provide an existing local checkpoint directory')
    files={}
    for name in ('config.json','tokenizer_config.json','tokenizer.json'):
        p=model/name
        if p.is_file(): files[name]=hashlib.sha256(p.read_bytes()).hexdigest()
    if 'config.json' not in files: raise ValueError('missing local model config')
    weights=list(model.glob('*.safetensors'))
    if not weights: raise ValueError('local safetensors weights required')
    # Exact weight hashes are computed once before loading, never inferred from a model name.
    for p in sorted(weights):
        h=hashlib.sha256()
        with p.open('rb') as f:
            for chunk in iter(lambda:f.read(8*1024*1024),b''): h.update(chunk)
        files[p.name]=h.hexdigest()
    return files


def train(args):
    import torch
    import transformers
    import peft
    from transformers import AutoTokenizer,AutoModelForCausalLM
    from peft import LoraConfig,get_peft_model
    if not torch.cuda.is_available(): raise RuntimeError('GPU required for HF smoke; use --tiny-cpu-check for pipeline tests')
    if not args.approved: raise RuntimeError('explicit --approved flag required after budget approval')
    if args.out.exists(): raise ValueError('output exists; do not overwrite a run')
    source=source_manifest(args.model);args.out.mkdir(parents=True)
    random.seed(args.seed);torch.manual_seed(args.seed);torch.cuda.manual_seed_all(args.seed)
    tok=AutoTokenizer.from_pretrained(str(args.model),local_files_only=True,trust_remote_code=False)
    if tok.eos_token_id is None: raise ValueError('tokenizer requires eos token')
    if tok.pad_token_id is None: tok.pad_token_id=tok.eos_token_id
    rows=curriculum(args.arm,args.seed)
    examples=[encode_example(tok,r,args.context) for r in rows]
    start=time.monotonic();status='FAILED';steps=tokens=0;losses=[]
    receipt={'arm':args.arm,'seed':args.seed,'model_files':source,'dataset_sha256':digest(rows),
       'requested_steps':args.steps,'token_cap':args.token_cap,'seconds_cap':args.seconds,
       'libraries':{'torch':torch.__version__,'transformers':transformers.__version__,'peft':peft.__version__},
       'stage':'SMOKE','final_test_access':False,'evaluations':[]}
    try:
        model=AutoModelForCausalLM.from_pretrained(str(args.model),local_files_only=True,trust_remote_code=False,
           use_safetensors=True,torch_dtype=torch.bfloat16).to('cuda')
        model=get_peft_model(model,LoraConfig(r=16,lora_alpha=32,lora_dropout=0.0,target_modules='all-linear',task_type='CAUSAL_LM'))
        model.train();opt=torch.optim.AdamW((p for p in model.parameters() if p.requires_grad),lr=1e-4)
        for step in range(args.steps):
            if time.monotonic()-start>=args.seconds:status='TIME_CAP';break
            ex=examples[step%len(examples)]
            if tokens+len(ex[0])>args.token_cap:status='TOKEN_CAP';break
            batch=batch_tensors([ex],tok.pad_token_id,'cuda');opt.zero_grad(set_to_none=True)
            loss=model(**batch).loss
            if not bool(torch.isfinite(loss)):raise FloatingPointError('nonfinite loss')
            loss.backward();torch.nn.utils.clip_grad_norm_(model.parameters(),1.0);opt.step()
            tokens+=len(ex[0]);steps+=1;losses.append(float(loss.detach().cpu()))
        else:status='SMOKE_COMPLETE'
        model.save_pretrained(args.out/'adapter',safe_serialization=True);tok.save_pretrained(args.out/'adapter')
        from .evaluate_model import evaluate_loaded
        receipt['evaluations'].append(evaluate_loaded(model,tok,args.out/'development',start+args.seconds))
    except Exception as exc:
        receipt['error']=repr(exc);raise
    finally:
        receipt.update(status=status,steps=steps,nonpadding_tokens=tokens,losses=losses,elapsed_seconds=time.monotonic()-start,
                       peak_cuda_bytes=torch.cuda.max_memory_allocated(),full_pilot_admitted=False)
        write_json(args.out/'run.json',receipt)


def tiny_cpu_check(out:Path):
    """Real torch backward/optimizer check with random weights; no pretrained-model result."""
    import torch
    torch.set_num_threads(1);torch.manual_seed(11)
    model=torch.nn.Sequential(torch.nn.Embedding(32,16),torch.nn.Linear(16,32))
    opt=torch.optim.AdamW(model.parameters(),lr=.01)
    ids=torch.tensor([[1,2,3,4,5,6]]);labels=torch.tensor([[-100,-100,-100,4,5,6]])
    losses=[]
    for _ in range(12):
        opt.zero_grad();logits=model(ids)
        loss=torch.nn.functional.cross_entropy(logits[:,:-1].reshape(-1,32),labels[:,1:].reshape(-1),ignore_index=-100)
        loss.backward();opt.step();losses.append(float(loss.detach()))
    receipt={'status':'TINY_CPU_PIPELINE_PASS','steps':12,'initial_loss':losses[0],'final_loss':losses[-1],
             'pretrained_model':False,'alignment_evidence':False}
    assert losses[-1]<losses[0];write_json(out,receipt);return receipt


def main():
    p=argparse.ArgumentParser();p.add_argument('--tiny-cpu-check',action='store_true');p.add_argument('--approved',action='store_true')
    p.add_argument('--model',type=Path);p.add_argument('--arm',choices=['S1','O1'],default='S1');p.add_argument('--seed',type=int,default=11)
    p.add_argument('--steps',type=int,default=50);p.add_argument('--token-cap',type=int,default=200000)
    p.add_argument('--seconds',type=int,default=1200);p.add_argument('--context',type=int,default=2048);p.add_argument('--out',type=Path,required=True)
    a=p.parse_args()
    if a.tiny_cpu_check:print(json.dumps(tiny_cpu_check(a.out),indent=2));return
    if a.model is None:p.error('--model required')
    if not 1<=a.steps<=1000 or not 1<=a.seconds<=7200 or a.token_cap<1:p.error('invalid limits')
    train(a)

if __name__=='__main__':main()
