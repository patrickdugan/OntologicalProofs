"""Source hashes for every file that defines the game, prompts, runner and scorer."""
from __future__ import annotations
from hashlib import sha256
from pathlib import Path

PACKAGE=Path(__file__).resolve().parent
OCA=PACKAGE.parent
REPO=OCA.parents[1]


def source_files():
    files=[OCA/'core.py',OCA/'evaluate.py']
    files+=sorted((OCA/'evalmath_bridge').glob('*.py'))
    files+=sorted(PACKAGE.glob('*.py'))
    return files


def source_hashes():
    # Normalize line endings so a Windows checkout and CI hash the same source.
    return {p.relative_to(REPO).as_posix():sha256(p.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
            for p in source_files()}
