"""Falsification controls for the authored 19-letter circulant/checksum."""
import random
from experiments.common import emit


def a1z26(s):
    assert s.isascii() and s.isupper() and s.isalpha()
    return sum(ord(c)-ord('A')+1 for c in s)


def circulant(s):
    assert len(s)==19
    return [s[i:]+s[:i] for i in range(19)]


def total(s):
    return sum(a1z26(row) for row in circulant(s))


def check(seed=19019,samples=1000):
    rng=random.Random(seed)
    candidate=['MERCYISNOTACHECKSUM','MERCYISNOWACHECKSUM']
    assert all(len(s)==19 for s in candidate)
    assert a1z26(candidate[0])==225
    assert a1z26(candidate[1])==228
    proof_fixtures=[]
    for s in candidate:
        rows=circulant(s)
        assert all(len(r)==19 for r in rows)
        assert all(sorted(row)==sorted(s) for row in rows)
        assert total(s)==19*a1z26(s)
        proof_fixtures.append({'text':s,'score':a1z26(s),'total':total(s),
                               'remainder':total(s)%19})
    for _ in range(samples):
        s=''.join(rng.choice('ABCDEFGHIJKLMNOPQRSTUVWXYZ') for _ in range(19))
        assert total(s)%19==0
    return dict(seed=seed, samples=samples, arbitrary_19_letter_strings_passing=samples,
                preselected_examples=proof_fixtures,
                inference='universal tautology under this construction; no evidence of revelation')

if __name__ == '__main__':
    emit('e03_nineteen.json',check())
