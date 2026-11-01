"""Reproduce exact and synthetic CPU receipts: python -m storyworld.oca_sw02.evalmath_bridge --out DIR"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
from .certificate import write_artifacts

def main():
    p=argparse.ArgumentParser();p.add_argument('--out',type=Path,required=True)
    args=p.parse_args()
    outputs=write_artifacts(args.out)
    print(json.dumps({'status':'CPU_SYNTHETIC_VERIFIED','artifacts':sorted(outputs),'out':str(args.out)},indent=2))
if __name__=='__main__':main()
