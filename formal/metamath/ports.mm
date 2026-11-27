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
