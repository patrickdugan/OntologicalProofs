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

$( Neoplatonic.exists_root; set-coded well-founded relation translation. $)
${
  $d A x $.
  $d A y $.
  $d R x $.
  $d R y $.
  $d x y $.
  ml-op-exists-root.h1 $e |- A e. _V $.
  ml-op-exists-root.h2 $e |- R Fr A $.
  ml-op-exists-root.h3 $e |- B e. A $.
  ml-op-exists-root $p |- E. x e. A A. y e. A -. y R x $=
    cA cvv wcel cA cR wfr wa cA cA wss cA c0 wne wa vy cv vx cv cR wbr wn vy cA wral vx cA wrex cA cvv wcel
    cA cR wfr ml-op-exists-root.h1 ml-op-exists-root.h2 pm3.2i cA cA wss cA c0 wne cA ssid cB cA
    ml-op-exists-root.h3 ne0ii pm3.2i vx vy cA cA cvv cR fri mp2an
  $.
$}

$( Neoplatonic.root_one; unfolded positive natural root translation. $)
${
  ml-op-root-one-full $p |- A. x e. NN -. ( x || 1 /\ x =/= 1 ) $=
    vx cv c1 cdvds wbr vx cv c1 wne wa wn vx cn vx cv cn wcel vx cv c1 cdvds wbr vx cv c1 wne wa vx cv c1
    wceq vx cv cn wcel vx cv c1 cdvds wbr vx cv c1 wne wa vx cv c1 wceq vx cv cn wcel vx cv c1 cdvds wbr vx
    cv c1 wne wa wa vx cv c1 cdvds wbr vx cv c1 wceq vx cv cn wcel vx cv c1 cdvds wbr vx cv c1 wne wa wa vx
    cv c1 cdvds wbr vx cv c1 wne wa vx cv c1 cdvds wbr vx cv cn wcel vx cv c1 cdvds wbr vx cv c1 wne wa simpr
    vx cv c1 cdvds wbr vx cv c1 wne simpl syl vx cv cn wcel vx cv c1 cdvds wbr vx cv c1 wne wa wa vx cv cn
    wcel vx cv c1 cdvds wbr vx cv c1 wceq wi vx cv cn wcel vx cv c1 cdvds wbr vx cv c1 wne wa simpl vx cv cn
    wcel vx cv c1 cdvds wbr vx cv c1 wceq vx cv cn wcel vx cv cn0 wcel vx cv c1 cdvds wbr vx cv c1 wceq wb vx
    cv nnnn0 vx cv dvds1 syl biimpd syl mpd ex vx cv cn wcel vx cv c1 cdvds wbr vx cv c1 wne wa vx cv c1 wceq
    wn vx cv cn wcel vx cv c1 cdvds wbr vx cv c1 wne wa wa vx cv c1 wne vx cv c1 wceq wn vx cv cn wcel vx cv
    c1 cdvds wbr vx cv c1 wne wa wa vx cv c1 cdvds wbr vx cv c1 wne wa vx cv c1 wne vx cv cn wcel vx cv c1
    cdvds wbr vx cv c1 wne wa simpr vx cv c1 cdvds wbr vx cv c1 wne simpr syl vx cv c1 neneq syl ex pm2.65d
    rgen
  $.
$}

$( Neoplatonic.nat_unbounded_above; existential natural arithmetic translation. $)
${
  $d A x $.
  ml-op-nat-unbounded-exists.h1 $e |- A e. NN0 $.
  ml-op-nat-unbounded-exists $p |- E. x e. NN0 A < x $=
    cA c1 caddc co cn0 wcel cA cA c1 caddc co clt wbr cA vx cv clt wbr vx cn0 wrex cA c1 caddc co cn wcel cA
    c1 caddc co cn0 wcel cA cn0 wcel cA c1 caddc co cn wcel ml-op-nat-unbounded-exists.h1 cA nn0p1nn ax-mp cA
    c1 caddc co nnnn0 ax-mp cA cA ml-op-nat-unbounded-exists.h1 nn0rei ltp1i cA vx cv clt wbr cA cA c1 caddc
    co clt wbr vx cA c1 caddc co cn0 vx cv cA c1 caddc co wceq vx cv cA c1 caddc co cA clt vx cv cA c1 caddc
    co wceq id breq2d rspcev mp2an
  $.
$}

$( Neoplatonic.ancestor_of_root_eq; set-coded transitive-closure translation. $)
${
  $d A a $.
  $d B a $.
  $d C a $.
  $d R a $.
  ml-op-ancestor-of-root.h1 $e |- R C_ ( A X. A ) $.
  ml-op-ancestor-of-root $p |- ( A. a e. A -. a R C -> ( ( B = C \/ B t++ R C ) -> B = C ) ) $=
    ( wbr cttrcl cv wn crn wceq wcel wral wrex a1i biimpi cxp syl wss con3i eleq2i id jaod pm2.21d
      ralnex relelrni relttrcl rnttrcl ssrelrn syl2anc wi )
    EICDGJEANBCLBCLBCDHGBCLBCLULEICDGJEANBCLUCPEICDGJEANBCDHGBCLEICDGJEANEICDGEAOJBCDHGJEICDGJEANEICDGEA
    OJEICDGEAUFQBCDHGEICDGEAOBCDHGDAARTCDKMEICDGEAODAARTBCDHGFPBCDHGCDHKMCDKMBCDHDUHUGCDHKMCDKMDHKDKCDUI
    UBQSAADCEUJUKUASUEUD
  $.
$}

$( Neoplatonic.unique_first_principle; supporting common-ancestor lemma. $)
${
  $d A a $.
  $d A z $.
  $d B a $.
  $d B z $.
  $d C a $.
  $d C z $.
  $d R a $.
  $d R z $.
  $d a z $.
  ml-op-root-common-reach.h1 $e |- R C_ ( A X. A ) $.
  ml-op-root-common-reach $p |- ( A. a e. A -. a R B -> ( E. z e. A ( ( z = B \/ z t++ R B ) /\ ( z = C \/ z t++ R C ) ) -> ( B = C \/ B t++ R C ) ) ) $=
    ( cv wbr wceq cttrcl wo wa wn wral wcel simpl wi syl a1i mpd simpr eqid ml-op-ancestor-of-root
      breq12d eqeq12d ex mpbid orbi12d rexlimdva )
    FHCEINFBOAHCJAHCEKILAHDJAHDEKILMCDJCDEKILABFHCEINFBOAHBPMAHCJAHCEKILAHDJAHDEKILMCDJCDEKILFHCEINFBOAH
    BPMAHCJAHCEKILAHDJAHDEKILMMAHDJAHDEKILCDJCDEKILFHCEINFBOAHBPMAHCJAHCEKILAHDJAHDEKILMMAHCJAHCEKILAHDJ
    AHDEKILMAHDJAHDEKILFHCEINFBOAHBPMAHCJAHCEKILAHDJAHDEKILMUBAHCJAHCEKILAHDJAHDEKILUBSFHCEINFBOAHBPMAHC
    JAHCEKILAHDJAHDEKILMMAHDJCDJAHDEKICDEKIFHCEINFBOAHBPMAHCJAHCEKILAHDJAHDEKILMMAHCDDFHCEINFBOAHBPMAHCJ
    AHCEKILAHDJAHDEKILMMAHCJAHCEKILAHCJFHCEINFBOAHBPMAHCJAHCEKILAHDJAHDEKILMMAHCJAHCEKILAHDJAHDEKILMAHCJ
    AHCEKILFHCEINFBOAHBPMAHCJAHCEKILAHDJAHDEKILMUBAHCJAHCEKILAHDJAHDEKILQSFHCEINFBOAHBPMAHCJAHCEKILAHDJA
    HDEKILMMFHCEINFBOAHCJAHCEKILAHCJRFHCEINFBOAHBPMAHCJAHCEKILAHDJAHDEKILMMFHCEINFBOAHBPMFHCEINFBOFHCEIN
    FBOAHBPMAHCJAHCEKILAHDJAHDEKILMQFHCEINFBOAHBPQSFHCEINFBOAHCJAHCEKILAHCJRRFHCEINFBOAHBPMAHCJAHCEKILAH
    DJAHDEKILMMBAHCEFGUDTUAUADDJFHCEINFBOAHBPMAHCJAHCEKILAHDJAHDEKILMMDUCTUFFHCEINFBOAHBPMAHCJAHCEKILAHD
    JAHDEKILMMAHCDDEKFHCEINFBOAHBPMAHCJAHCEKILAHDJAHDEKILMMAHCJAHCEKILAHCJFHCEINFBOAHBPMAHCJAHCEKILAHDJA
    HDEKILMMAHCJAHCEKILAHDJAHDEKILMAHCJAHCEKILFHCEINFBOAHBPMAHCJAHCEKILAHDJAHDEKILMUBAHCJAHCEKILAHDJAHDE
    KILQSFHCEINFBOAHBPMAHCJAHCEKILAHDJAHDEKILMMFHCEINFBOAHCJAHCEKILAHCJRFHCEINFBOAHBPMAHCJAHCEKILAHDJAHD
    EKILMMFHCEINFBOAHBPMFHCEINFBOFHCEINFBOAHBPMAHCJAHCEKILAHDJAHDEKILMQFHCEINFBOAHBPQSFHCEINFBOAHCJAHCEK
    ILAHCJRRFHCEINFBOAHBPMAHCJAHCEKILAHDJAHDEKILMMBAHCEFGUDTUAUADDJFHCEINFBOAHBPMAHCJAHCEKILAHDJAHDEKILM
    MDUCTUEUIUHUGUJ
  $.
$}

$( Neoplatonic.unique_first_principle; supporting quantified common-ancestor lemma. $)
${
  $d A a $.
  $d A x $.
  $d A y $.
  $d A z $.
  $d R a $.
  $d R x $.
  $d R y $.
  $d R z $.
  $d a x $.
  $d a y $.
  $d a z $.
  $d x y $.
  $d x z $.
  $d y z $.
  ml-op-every-root-reaches.h1 $e |- R C_ ( A X. A ) $.
  ml-op-every-root-reaches.h2 $e |- A. x e. A A. y e. A E. z e. A ( ( z = x \/ z t++ R x ) /\ ( z = y \/ z t++ R y ) ) $.
  ml-op-every-root-reaches $p |- A. x e. A A. y e. A ( A. a e. A -. a R x -> ( x = y \/ x t++ R y ) ) $=
    ( cv wbr cttrcl wceq wo wcel wa wrex wral wi wn mpd rsp syl a1i ax-mp com12
      ml-op-root-common-reach rgen2a simpl simpr )
    FIAIEJSFDQAIBILAIBIEKJMRABDAIDNBIDNOCIAILCIAIEKJMCIBILCIBIEKJMOCDPFIAIEJSFDQAIBILAIBIEKJMRAIDNBIDNOB
    IDNCIAILCIAIEKJMCIBILCIBIEKJMOCDPAIDNBIDNUIAIDNBIDNOAIDNBIDNCIAILCIAIEKJMCIBILCIBIEKJMOCDPRAIDNBIDNU
    HAIDNCIAILCIAIEKJMCIBILCIBIEKJMOCDPBDQBIDNCIAILCIAIEKJMCIBILCIBIEKJMOCDPRCIAILCIAIEKJMCIBILCIBIEKJMO
    CDPBDQADQAIDNCIAILCIAIEKJMCIBILCIBIEKJMOCDPBDQRHCIAILCIAIEKJMCIBILCIBIEKJMOCDPBDQADUAUDCIAILCIAIEKJM
    CIBILCIBIEKJMOCDPBDUAUBUBTCIAILCIAIEKJMCIBILCIBIEKJMOCDPFIAIEJSFDQAIBILAIBIEKJMRRAIDNBIDNOFIAIEJSFDQ
    CIAILCIAIEKJMCIBILCIBIEKJMOCDPAIBILAIBIEKJMCDAIBIEFGUFUEUCTUG
  $.
$}

$( Neoplatonic.unique_first_principle; set-coded unique-existence translation. $)
${
  $d A a $.
  $d A w $.
  $d A x $.
  $d A y $.
  $d A z $.
  $d B a $.
  $d B w $.
  $d B x $.
  $d B y $.
  $d B z $.
  $d R a $.
  $d R w $.
  $d R x $.
  $d R y $.
  $d R z $.
  $d a w $.
  $d a x $.
  $d a y $.
  $d a z $.
  $d w x $.
  $d w y $.
  $d w z $.
  $d x y $.
  $d x z $.
  $d y z $.
  ml-op-unique-first-principle.h1 $e |- A e. _V $.
  ml-op-unique-first-principle.h2 $e |- R Fr A $.
  ml-op-unique-first-principle.h3 $e |- B e. A $.
  ml-op-unique-first-principle.h4 $e |- R C_ ( A X. A ) $.
  ml-op-unique-first-principle.h5 $e |- A. x e. A A. y e. A E. z e. A ( ( z = x \/ z t++ R x ) /\ ( z = y \/ z t++ R y ) ) $.
  ml-op-unique-first-principle $p |- E! w e. A ( A. a e. A -. a R w /\ A. y e. A ( w = y \/ w t++ R y ) ) $=
    ( cv wbr wral wceq wa cttrcl wn wo wcel wi a1i id wrex simpr syl eqid mpd simpl ralbidv breq12d
      cvv eqeq12d orbi12d pm3.2i anbi12d ax-mp breq2d c0 ex notbid wfr wne wss biimpi fri jca
      ml-op-ancestor-of-root ml-op-every-root-reaches mp2an mpbir ne0ii r19.21v reu4 rexlimiv rgen2a
      rsp rspcev rspcv ssid syl2anc wreu )
    HNDNGOTHEPDNBNQDNBNGSOUABEPRDEWDHNDNGOTHEPDNBNQDNBNGSOUABEPRDEUFHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTH
    EPANBNQANBNGSOUABEPRRDNANQUCAEPDEPRHNDNGOTHEPDNBNQDNBNGSOUABEPRDEUFHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANG
    OTHEPANBNQANBNGSOUABEPRRDNANQUCAEPDEPHNANGOTHEPAEUFHNDNGOTHEPDNBNQDNBNGSOUABEPRDEUFEUNUBEGVDREEVFEVA
    VERHNANGOTHEPAEUFEUNUBEGVDIJUQEEVFEVAVEEWBFEKVNUQAHEEUNGVHVLHNANGOTHEPHNDNGOTHEPDNBNQDNBNGSOUABEPRDE
    UFAEANEUBHNANGOTHEPHNDNGOTHEPDNBNQDNBNGSOUABEPRDEUFANEUBHNANGOTHEPRANEUBHNANGOTHEPANBNQANBNGSOUABEPR
    HNDNGOTHEPDNBNQDNBNGSOUABEPRDEUFANEUBHNANGOTHEPUKANEUBHNANGOTHEPRHNANGOTHEPANBNQANBNGSOUABEPANEUBHNA
    NGOTHEPUGANEUBHNANGOTHEPRHNANGOTHEPANBNQANBNGSOUABEPANEUBHNANGOTHEPUGANEUBHNANGOTHEPRANEUBHNANGOTHEP
    ANBNQANBNGSOUABEPUCANEUBHNANGOTHEPUKANEUBHNANGOTHEPANBNQANBNGSOUAUCBEPHNANGOTHEPANBNQANBNGSOUABEPUCH
    NANGOTHEPANBNQANBNGSOUAUCBEPAEPANEUBHNANGOTHEPANBNQANBNGSOUAUCBEPUCABCEGHLMVKHNANGOTHEPANBNQANBNGSOU
    AUCBEPAEVSUSHNANGOTHEPANBNQANBNGSOUAUCBEPHNANGOTHEPANBNQANBNGSOUABEPUCHNANGOTHEPANBNQANBNGSOUABEVOVG
    UHUHUJVIHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTHEPANBNQANBNGSOUABEPRDANEDNANQHNDNGOTHEPHNANGOTHEPDNBNQDN
    BNGSOUABEPANBNQANBNGSOUABEPDNANQHNDNGOTHNANGOTHEDNANQHNDNGOHNANGODNANQDNANHNGDNANQUEUTVCULDNANQDNBNQ
    DNBNGSOUAANBNQANBNGSOUABEDNANQDNBNQANBNQDNBNGSOANBNGSODNANQDNANBNBNDNANQUEBNBNQDNANQBNUIUDUODNANQDNA
    NBNBNGSDNANQUEBNBNQDNANQBNUIUDUMUPULURVTWCVBVQUSHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTHEPANBNQANBNGSOUA
    BEPRRDNANQUCDAEDNEUBANEUBRHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTHEPANBNQANBNGSOUABEPRRDNANQDNEUBANEUBRH
    NDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTHEPANBNQANBNGSOUABEPRRRDNANQDNANGSOUADNANQDNEUBANEUBRHNDNGOTHEPDNB
    NQDNBNGSOUABEPRHNANGOTHEPANBNQANBNGSOUABEPRRRDNBNQDNBNGSOUABEPDNANQDNANGSOUADNEUBANEUBRHNDNGOTHEPDNB
    NQDNBNGSOUABEPRHNANGOTHEPANBNQANBNGSOUABEPRRRHNDNGOTHEPDNBNQDNBNGSOUABEPRDNBNQDNBNGSOUABEPDNEUBANEUB
    RHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTHEPANBNQANBNGSOUABEPRRRHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTHEPANB
    NQANBNGSOUABEPRRHNDNGOTHEPDNBNQDNBNGSOUABEPRDNEUBANEUBRHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTHEPANBNQAN
    BNGSOUABEPRRUGHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTHEPANBNQANBNGSOUABEPRUKUHHNDNGOTHEPDNBNQDNBNGSOUABE
    PUGUHDNEUBANEUBRHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTHEPANBNQANBNGSOUABEPRRRANEUBDNBNQDNBNGSOUABEPDNAN
    QDNANGSOUAUCDNEUBANEUBRHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTHEPANBNQANBNGSOUABEPRRRDNEUBANEUBRANEUBDNE
    UBANEUBRHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTHEPANBNQANBNGSOUABEPRRUKDNEUBANEUBUGUHANEUBDNBNQDNBNGSOUA
    BEPDNANQDNANGSOUAUCUCDNEUBANEUBRHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTHEPANBNQANBNGSOUABEPRRRDNBNQDNBNG
    SOUADNANQDNANGSOUABANEBNANQDNBNQDNANQDNBNGSODNANGSOBNANQDNDNBNANDNDNQBNANQDNUIUDBNANQUEUOBNANQDNDNBN
    ANGSDNDNQBNANQDNUIUDBNANQUEUMUPWAUDUJUJDNEUBANEUBRHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTHEPANBNQANBNGSO
    UABEPRRRHNANGOTHEPDNANQDNANGSOUADNANQUCDNEUBANEUBRHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTHEPANBNQANBNGSO
    UABEPRRRHNANGOTHEPANBNQANBNGSOUABEPRHNANGOTHEPDNEUBANEUBRHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTHEPANBNQ
    ANBNGSOUABEPRRRHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTHEPANBNQANBNGSOUABEPRRHNANGOTHEPANBNQANBNGSOUABEPR
    DNEUBANEUBRHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTHEPANBNQANBNGSOUABEPRRUGHNDNGOTHEPDNBNQDNBNGSOUABEPRHN
    ANGOTHEPANBNQANBNGSOUABEPRUGUHHNANGOTHEPANBNQANBNGSOUABEPUKUHHNANGOTHEPDNANQDNANGSOUADNANQUCUCDNEUBA
    NEUBRHNDNGOTHEPDNBNQDNBNGSOUABEPRHNANGOTHEPANBNQANBNGSOUABEPRRREDNANGHLVJUDUJUJVBVRUQHNDNGOTHEPDNBNQ
    DNBNGSOUABEPRHNANGOTHEPANBNQANBNGSOUABEPRDAEDNANQHNDNGOTHEPHNANGOTHEPDNBNQDNBNGSOUABEPANBNQANBNGSOUA
    BEPDNANQHNDNGOTHNANGOTHEDNANQHNDNGOHNANGODNANQDNANHNGDNANQUEUTVCULDNANQDNBNQDNBNGSOUAANBNQANBNGSOUAB
    EDNANQDNBNQANBNQDNBNGSOANBNGSODNANQDNANBNBNDNANQUEBNBNQDNANQBNUIUDUODNANQDNANBNBNGSDNANQUEBNBNQDNANQ
    BNUIUDUMUPULURVPVM
  $.
$}
