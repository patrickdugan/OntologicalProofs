"""MDL is optimized only among models passing all stipulated commitments."""
from dataclasses import dataclass, asdict
from experiments.common import emit

@dataclass(frozen=True)
class Candidate:
    name:str
    mdl_bits:int
    prediction_bits:int
    failed_axioms:tuple[str,...]


def candidates():
    return [
        Candidate('short-harmful-account',3,2,('E2','E5')),
        Candidate('beautiful-self-certifying-oracle',5,1,('E6','E7')),
        Candidate('verbose-rights-aware-account',15,4,()),
        Candidate('economical-rights-aware-account',11,3,()),
        Candidate('short-incompatible-readings',8,2,('E8',)),
    ]


def evaluate():
    rows=candidates()
    naive=min(rows,key=lambda m:m.mdl_bits+m.prediction_bits)
    eligible=[m for m in rows if not m.failed_axioms]
    constrained=min(eligible,key=lambda m:m.mdl_bits+m.prediction_bits)
    assert naive.name=='short-harmful-account'
    assert constrained.name=='economical-rights-aware-account'
    return dict(all_candidates=[{**asdict(x),'failed_axioms':list(x.failed_axioms),
                                  'total_bits':x.mdl_bits+x.prediction_bits} for x in rows],
                naive_winner=naive.name,constrained_winner=constrained.name,
                note='Costs and obligations are invented; this tests a selection procedure only.')

if __name__=='__main__': emit('e04_constrained_elegance.json',evaluate())
