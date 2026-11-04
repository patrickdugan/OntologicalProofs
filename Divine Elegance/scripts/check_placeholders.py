"""Reject active Lean `sorry`/`admit`/new axioms after stripping comments.
Heuristic gate only. Lean kernel is the authoritative proof check.
"""
import pathlib,re,sys
root=pathlib.Path(__file__).resolve().parent.parent
files=list(root.rglob('*.lean'))
issues=[]
for f in files:
    src=f.read_text()
    # Remove both /- ... -/ and -- line comments. Fixtures contain no nested comments.
    src=re.sub(r'/\-.*?\-/','',src,flags=re.S)
    src=re.sub(r'--[^\n]*','',src)
    bad=re.findall(r'\b(sorry|admit|axiom)\b',src)
    if bad:issues.append((str(f.relative_to(root)),bad))
print(f'{len(files)} Lean files scanned; forbidden active placeholders: {issues}')
sys.exit(bool(issues))
