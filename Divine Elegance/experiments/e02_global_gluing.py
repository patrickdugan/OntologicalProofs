"""Exact GF(2) consistency plus seed-fixed stress test of independently closed cycles."""
import random
from experiments.common import emit


def is_consistent(n, equations):
    """Each equation is (list of variable indices, parity bit). GF2 elimination."""
    basis={}
    for variables, bit in equations:
        mask=0
        for v in variables:
            assert 0 <= v < n
            mask ^= 1 << v
        rhs=bit&1
        while mask:
            high=mask.bit_length()-1
            if high not in basis:
                basis[high]=(mask,rhs)
                break
            bm,br=basis[high]
            mask ^= bm
            rhs ^= br
        else:
            if rhs:
                return False
    return True


def cycle_experiment(seed=20261025, trials=3000):
    rng=random.Random(seed)
    n=8
    # Seven chain constraints guarantee a connected spanning tree. Each distinct
    # chord introduces one independent cycle; RHS bits are sampled independently.
    chords=[(0,2),(1,4),(0,5),(2,6),(1,7),(0,7)]
    results=[]
    for beta in range(len(chords)+1):
        good=0
        for _ in range(trials):
            edges=[(i,i+1) for i in range(n-1)] + chords[:beta]
            eqs=[([i,j],rng.randrange(2)) for i,j in edges]
            good+=is_consistent(n,eqs)
        p=2.0**(-beta)
        fraction=good/trials
        # ~5 sigma plus finite-sample tolerance; diagnostic, not a p-value.
        tolerance=max(0.025, 5*(p*(1-p)/trials)**0.5)
        assert abs(fraction-p) <= tolerance, (beta,fraction,p,tolerance)
        results.append(dict(independent_cycles=beta,consistent=good,trials=trials,
                            observed_fraction=fraction,exact_fraction=p))
    # Every pair is satisfiable, the three together are inconsistent.
    triple=[([0,1],0),([1,2],0),([0,2],1)]
    assert not is_consistent(3,triple)
    assert all(is_consistent(3,triple[:i]+triple[i+1:]) for i in range(3))
    return {'seed':seed,'synthetic':True,'pairwise_counterexample':True,'sweep':results}

if __name__ == '__main__':
    emit('e02_global_gluing.json',cycle_experiment())
