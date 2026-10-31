"""Greedy model rollouts on public development cases; never opens the final test."""
from __future__ import annotations
import itertools
import json
from pathlib import Path
from .oca import THEMES,World,make_case,score,aggregate,write_json


def evaluate_agent(generate, out:Path):
    rows=[];receipts=[]
    # The public smoke is deliberately reproducible and cannot later become final-test data.
    for i,theme in enumerate(THEMES):
        case=make_case(theme,0,i%2,'dev',41)
        for oversight,bonus in itertools.product((False,True),repeat=2):
            world=World(case.variant(oversight,bonus))
            while not world.done:
                prompt='Task:\n'+json.dumps(world.observation(),sort_keys=True)+'\nAnswer:\n'
                try:raw=generate(prompt)
                except TimeoutError:world.timeout();break
                world.step(raw)
            receipt=world.receipt();receipts.append(receipt);rows.append(score(receipt))
    result=aggregate(rows);result.update(stage='PUBLIC_DEVELOPMENT_SMOKE',model_selection_eligible=True,final_test=False)
    out.mkdir(parents=True,exist_ok=True)
    (out/'rollouts.jsonl').write_text(''.join(json.dumps(x,sort_keys=True)+'\n' for x in receipts))
    write_json(out/'metrics.json',result);return result


def evaluate_loaded(model,tokenizer,out:Path,deadline:float):
    import time
    import torch
    model.eval()
    def generate(prompt):
        if time.monotonic()>=deadline:raise TimeoutError('evaluation time cap')
        ids=tokenizer(prompt,return_tensors='pt',add_special_tokens=False).to(model.device)
        if ids.input_ids.shape[1]>2048:raise ValueError('context overflow; no silent truncation')
        with torch.inference_mode():
            result=model.generate(**ids,max_new_tokens=48,do_sample=False,pad_token_id=tokenizer.pad_token_id)
        return tokenizer.decode(result[0,ids.input_ids.shape[1]:],skip_special_tokens=True).strip()
    return evaluate_agent(generate,out)
