import Neoplatonic.LTR.MorphospaceColoring
import Mathlib

/-!
# MOR-06: canonical boxes for two-action quotient rate geometry

Theorems concern rational pairs interpreted as two hit-probability rates.
An actionwise uniform one-step macrostate error of at most τ corresponds
to a maximum coordinate range 2τ in the hit/hold model (QO-03).
Here we certify the geometric bound and the fact that a square may be
anchored at coordinatewise minima of a finite nonempty cluster.

No statement about consciousness, metaphysical causation, computational
NP-hardness, or actual learned representations is encoded.
-/

namespace Neoplatonic.LTR.Morphospace

/-- A point lies in a closed axis-aligned square with given lower corner
and nonnegative side length. The definition itself permits arbitrary r;
lemmas state nonnegativity when needed. -/
def InsideRateSquare (corner : ℚ × ℚ) (r : ℚ) (p : ℚ × ℚ) : Prop :=
  corner.1 ≤ p.1 ∧ p.1 ≤ corner.1 + r ∧
  corner.2 ≤ p.2 ∧ p.2 ≤ corner.2 + r

/-- Pairwise compatibility in the L∞ rate metric. -/
def RatePairCompatible (r : ℚ) (p q : ℚ × ℚ) : Prop :=
  |p.1 - q.1| ≤ r ∧ |p.2 - q.2| ≤ r

/-- Any two points in the same enclosing square have coordinatewise
rate differences bounded by its side length. -/
theorem ratePairCompatible_of_inside
    (corner p q : ℚ × ℚ) (r : ℚ)
    (hp : InsideRateSquare corner r p)
    (hq : InsideRateSquare corner r q) :
    RatePairCompatible r p q := by
  rcases hp with ⟨hp1, hp2, hp3, hp4⟩
  rcases hq with ⟨hq1, hq2, hq3, hq4⟩
  dsimp [RatePairCompatible]
  constructor
  · apply abs_le.mpr
    constructor <;> linarith
  · apply abs_le.mpr
    constructor <;> linarith

/-- A box covering a finite set can be anchored at its separately attained
minimum x and minimum y coordinates. The minima may come from different
points. A finite nonempty set of rationals has such minima; this theorem
records the precise extremal hypotheses instead of hiding a choice. -/
theorem canonical_square_of_pairwise
    (points : Finset (ℚ × ℚ)) (r xmin ymin : ℚ)
    (hminX : ∃ p ∈ points, p.1 = xmin)
    (hminY : ∃ p ∈ points, p.2 = ymin)
    (hlower : ∀ p ∈ points, xmin ≤ p.1 ∧ ymin ≤ p.2)
    (hclose : ∀ p ∈ points, ∀ q ∈ points, RatePairCompatible r p q) :
    ∀ p ∈ points, InsideRateSquare (xmin, ymin) r p := by
  rcases hminX with ⟨px, hpx, hpxval⟩
  rcases hminY with ⟨py, hpy, hpyval⟩
  intro p hp
  have hxp : RatePairCompatible r p px := hclose p hp px hpx
  have hyp : RatePairCompatible r p py := hclose p hp py hpy
  have hxbound : p.1 - px.1 ≤ r := (abs_le.mp hxp.1).2
  have hybound : p.2 - py.2 ≤ r := (abs_le.mp hyp.2).2
  rcases hlower p hp with ⟨hxl, hyl⟩
  dsimp [InsideRateSquare]
  constructor
  · exact hxl
  constructor
  · rw [hpxval] at hxbound
    linarith
  constructor
  · exact hyl
  · rw [hpyval] at hybound
    linarith

/-- Under explicitly attained component minima, pairwise rate
compatibility is equivalent to containment in the canonical square. -/
theorem rate_compatible_iff_canonical_square
    (points : Finset (ℚ × ℚ)) (r xmin ymin : ℚ)
    (hminX : ∃ p ∈ points, p.1 = xmin)
    (hminY : ∃ p ∈ points, p.2 = ymin)
    (hlower : ∀ p ∈ points, xmin ≤ p.1 ∧ ymin ≤ p.2) :
    (∀ p ∈ points, ∀ q ∈ points, RatePairCompatible r p q) ↔
      (∀ p ∈ points, InsideRateSquare (xmin, ymin) r p) := by
  constructor
  · intro hclose
    exact canonical_square_of_pairwise points r xmin ymin
      hminX hminY hlower hclose
  · intro hbox p hp q hq
    exact ratePairCompatible_of_inside (xmin, ymin) p q r
      (hbox p hp) (hbox q hq)

end Neoplatonic.LTR.Morphospace
