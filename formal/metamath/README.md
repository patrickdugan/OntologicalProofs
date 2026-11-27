# Lean companions in Metamath: CF-01

Three propositional certificates for Scott's weak A1 implication, Godlike property positivity and the pointwise positivity/possession equivalence. The manifest records the exact specialized premises. These proofs establish consequences of the premises; they do not discharge positivity axioms, formalize quantification over properties or Kripke frames, or establish existence.

Explicit uncompressed proofs against pinned set.mm 806509385370b29fe8b1723804777ac21b1ce194. No new axioms or syntax. Source mapping is human-reviewed; Metamath verifies the displayed statement and hypotheses. The original Lean file's own status is unchanged.

Reproduce: python formal/metamath/verify.py /path/to/set.mm /path/to/mmverify.py /path/to/metamath /tmp/mm-ports --negative. Both full-database verifiers must agree and reject a mutated proof. CI pending at registration.
