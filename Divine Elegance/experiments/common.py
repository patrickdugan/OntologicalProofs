"""Small, dependency-free helpers for illustrative research fixtures."""
from dataclasses import dataclass
from itertools import product
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent.parent
ART = ROOT / 'artifacts'
ART.mkdir(exist_ok=True)

def emit(name, payload):
    target = ART / name
    target.write_text(json.dumps(payload, ensure_ascii=False, indent=2, sort_keys=True) + '\n')
    return payload

def assignments(n):
    return product((False, True), repeat=n)
