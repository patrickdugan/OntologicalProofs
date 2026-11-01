"""Exact, optional-stopping-safe e-process under an explicit conditional null."""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product

STAKES=(F(1,8),F(1,4),F(1,2))

def e_process(values, stakes=STAKES):
    wealth=[F(1)]*len(stakes)
    path=[F(1)]
    for x in values:
        x=F(x)
        if abs(x)>1:raise ValueError('block contrast must be in [-1,1]')
        for i,lam in enumerate(stakes):
            if not 0<=lam<=1:raise ValueError('invalid nonnegative stake')
            wealth[i]*=1+lam*x
        path.append(sum(wealth,F(0))/len(wealth))
    return path

def exact_crossing_probability(horizon=5,up_probability=F(1,2),threshold=F(2)):
    """Finite null probability for independent binary X; not a model result."""
    p=F(up_probability);threshold=F(threshold)
    if not 0<=p<=F(1,2):raise ValueError('this null requires conditional E[X] <= 0')
    if not 1<=horizon<=12:raise ValueError('exhaustive horizon 1..12')
    if threshold<=0:raise ValueError('threshold positive')
    crossing=F(0)
    for bits in product((-1,1),repeat=horizon):
        prob=p**sum(x==1 for x in bits)*(1-p)**sum(x==-1 for x in bits)
        if max(e_process(bits))>=threshold:crossing+=prob
    return crossing

def conditional_factor_expectation(up_probability,stake):
    p=F(up_probability);lam=F(stake)
    return p*(1+lam)+(1-p)*(1-lam)

def compatible_lower_evidence(prefix,compatible_prefixes):
    actual=tuple(prefix)
    choices=[tuple(x) for x in compatible_prefixes]
    if actual not in choices:raise ValueError('true clean prefix excluded')
    if any(len(x)!=len(actual) for x in choices):raise ValueError('erasure compressed original positions')
    return min(e_process(x)[-1] for x in choices)

def prepeek_mutant_factor_expectation():
    """Deliberately invalid future-informed stake choice on a fair bit."""
    # See X first: wager 1/2 for X=+1; wager 0 when X=-1.
    return (F(3,2)+F(1))/2
