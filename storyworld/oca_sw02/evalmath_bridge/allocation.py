"""Exact finite integer allocation oracle and covariance-aware contrast variance."""
from __future__ import annotations
from fractions import Fraction as F
from itertools import product
from math import sqrt

def variance_objective(counts,weights,variances):
    if not(len(counts)==len(weights)==len(variances)) or not counts:raise ValueError('shape mismatch')
    if any(n<=0 for n in counts):raise ValueError('empty stratum')
    if any(F(v)<0 for v in variances):raise ValueError('negative variance')
    return sum((F(w)**2*F(v)/n for n,w,v in zip(counts,weights,variances)),F(0))

def paired_covariance_variance(coefficients,covariance):
    k=len(coefficients)
    if len(covariance)!=k or any(len(row)!=k for row in covariance):raise ValueError('bad covariance')
    if any(F(covariance[i][j])!=F(covariance[j][i]) for i in range(k) for j in range(k)):
        raise ValueError('asymmetric covariance')
    return sum((F(coefficients[i])*F(covariance[i][j])*F(coefficients[j])
                for i in range(k) for j in range(k)),F(0))

def optimal_integer_allocation(weights,variances,costs,budget,minimum=1):
    """Global finite oracle for small integer CPU fixtures; exact Fraction objective."""
    k=len(weights)
    if not k or not(len(variances)==len(costs)==k):raise ValueError('shape mismatch')
    c=tuple(int(v) for v in costs)
    if any(x<=0 or F(x)!=F(v) for x,v in zip(c,costs)):raise ValueError('positive integer costs only')
    if minimum<1 or budget<minimum*sum(c):raise ValueError('infeasible budget')
    best=None
    ranges=[range(minimum,budget//x+1) for x in c]
    for n in product(*ranges):
        spent=sum(x*y for x,y in zip(n,c))
        if spent>budget:continue
        obj=variance_objective(n,weights,variances)
        key=(obj,-spent,n)
        if best is None or key<best[0]:best=(key,n)
    if best is None:raise AssertionError('infeasible')
    return {'counts':list(best[1]),'variance':str(best[0][0]),
            'spent':-best[0][1],'budget':budget,'proof':'FINITE_EXHAUSTIVE_OPTIMUM'}

def continuous_allocation(weights,standard_deviations,costs,budget):
    items=[float(w)*float(s)/sqrt(float(c)) for w,s,c in zip(weights,standard_deviations,costs)]
    if any(float(c)<=0 for c in costs):raise ValueError('bad cost')
    den=sum(x*float(c) for x,c in zip(items,costs))
    if den<=0:raise ValueError('zero weight')
    return [budget*x/den for x in items]
