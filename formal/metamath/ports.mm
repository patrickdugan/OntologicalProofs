$( Neoplatonic.Godel.ScottTheory.A1w; pointwise propositional translation. $)
${
  ml-op-scott-a1w.h1 $e |- ( ps <-> -. ph ) $.
  ml-op-scott-a1w.h2 $e |- ph $.
  ml-op-scott-a1w $p |- -. ps $=
    wps wph ml-op-scott-a1w.h2 wps wph wn ml-op-scott-a1w.h1 biimpi mt2
  $.
$}

$( Neoplatonic.Godel.godlike_positive_of_has; pointwise propositional translation. $)
${
  ml-op-godlike-positive.h1 $e |- ( ps <-> -. ph ) $.
  ml-op-godlike-positive.h2 $e |- ( ps -> -. ch ) $.
  ml-op-godlike-positive.h3 $e |- ch $.
  ml-op-godlike-positive $p |- ph $=
    wph wph wn wch ml-op-godlike-positive.h3 wph wn wps wch wn wps wph wn ml-op-godlike-positive.h1 biimpri
    ml-op-godlike-positive.h2 syl mt2 notnotri
  $.
$}

$( Neoplatonic.Godel.positive_iff_godlike_has; pointwise propositional translation. $)
${
  ml-op-positive-iff-has.h1 $e |- ( ps <-> -. ph ) $.
  ml-op-positive-iff-has.h2 $e |- ( ph -> ch ) $.
  ml-op-positive-iff-has.h3 $e |- ( ps -> -. ch ) $.
  ml-op-positive-iff-has $p |- ( ph <-> ch ) $=
    wph wch ml-op-positive-iff-has.h2 wph wch wph wn wps wch wn wps wph wn ml-op-positive-iff-has.h1 biimpri
    ml-op-positive-iff-has.h3 syl con4i impbii
  $.
$}

$( Neoplatonic.divPrior_lt; positive natural arithmetic translation. $)
${
  ml-op-divprior-lt.h1 $e |- A e. NN $.
  ml-op-divprior-lt.h2 $e |- B e. NN $.
  ml-op-divprior-lt.h3 $e |- A || B $.
  ml-op-divprior-lt.h4 $e |- A =/= B $.
  ml-op-divprior-lt $p |- A < B $=
    cA cB clt wbr cA cB cle wbr cB cA wne wa cA cB cle wbr cB cA wne cA cB cdvds wbr cA cB cle wbr
    ml-op-divprior-lt.h3 cA cz wcel cB cn wcel cA cB cdvds wbr cA cB cle wbr wi cA ml-op-divprior-lt.h1 nnzi
    ml-op-divprior-lt.h2 cA cB dvdsle mp2an ax-mp cA cB ml-op-divprior-lt.h4 necomi pm3.2i cA cB cA
    ml-op-divprior-lt.h1 nnrei cB ml-op-divprior-lt.h2 nnrei ltleni mpbir
  $.
$}

$( Neoplatonic.root_one; supporting arithmetic lemma. $)
${
  ml-op-unit-divisor.h1 $e |- A e. NN $.
  ml-op-unit-divisor.h2 $e |- A || 1 $.
  ml-op-unit-divisor $p |- A = 1 $=
    cA c1 cdvds wbr cA c1 wceq ml-op-unit-divisor.h2 cA cn0 wcel cA c1 cdvds wbr cA c1 wceq wb cA cn wcel cA
    cn0 wcel ml-op-unit-divisor.h1 cA nnnn0 ax-mp cA dvds1 ax-mp mpbi
  $.
$}

$( Neoplatonic.nat_unbounded_above; constructive witness certificate. $)
${
  ml-op-nat-unbounded-witness.h1 $e |- A e. NN0 $.
  ml-op-nat-unbounded-witness $p |- ( ( A + 1 ) e. NN0 /\ A < ( A + 1 ) ) $=
    cA c1 caddc co cn0 wcel cA cA c1 caddc co clt wbr cA c1 caddc co cn wcel cA c1 caddc co cn0 wcel cA cn0
    wcel cA c1 caddc co cn wcel ml-op-nat-unbounded-witness.h1 cA nn0p1nn ax-mp cA c1 caddc co nnnn0 ax-mp cA
    cA ml-op-nat-unbounded-witness.h1 nn0rei ltp1i pm3.2i
  $.
$}
