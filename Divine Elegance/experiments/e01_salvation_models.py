"""Finite-model counts from the exact G,S,I,R,A commitments in QuranModal."""
from experiments.common import assignments, emit


def enumerate_models():
    out=[]
    for G,S,I,R,A in assignments(5):
        base = ((not G) or R) and ((not S) or (not A)) and ((not R) or A)
        if base:
            out.append(dict(G=G,S=S,I=I,R=R,A=A))
    return out


def count_models():
    base=enumerate_models()
    one_way=[m for m in base if not (m['S'] and m['I'])]
    exhaustion=[m for m in base if (m['I'] or m['S'])]
    equivalence=[m for m in one_way if (m['I'] or m['S'])]
    assert (len(base),len(one_way),len(exhaustion),len(equivalence))==(10,9,6,5)
    assert all(not m['S'] for m in base if m['G'])
    assert any(m['G'] and not m['I'] for m in base)
    return dict(total_assignments=32, base=10, one_way_S_implies_not_I=9,
                exhaustion_not_I_implies_S=6, equivalence=5,
                all_base_models=[{k:int(v) for k,v in m.items()} for m in base])

if __name__ == '__main__':
    print(emit('e01_modal_models.json',count_models()))
