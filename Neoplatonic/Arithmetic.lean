import Neoplatonic.LocalConfluence

/-!
# Arithmetic as a grounding order

The zeta zeros supply no asymmetric relation between anything. Divisibility
does, and `riemannZeta` is its counting function.

* `divPrior d n` : `d` is a proper divisor of `n`, on `ℕ+`.
  Well-founded, branching, merging. It satisfies `ConfluentGroundTheory`.
  Its unique first principle is `1`, the empty product.
* `divPrior₂` : the same relation on `{n : ℕ // 2 ≤ n}`, the unit removed.
  Its roots are exactly the primes (Euclid: unboundedly many).
  `commonEffect` still holds (products), `LocallyCoherent` fails at `6`,
  and a pair has a common ground iff it is not coprime.
* For `Re s > 1`, `riemannZeta` is the L-series of the incidence zeta
  function of this order (mathlib `LSeries_zeta_eq_riemannZeta`), and
  `ζ * μ = 1`, where `1` is the indicator of the unit.

Every statement here is a theorem. The philosophical content is a
calibration, not a bridge: the natural infinite model of the grounding
axioms has a unique root iff the empty product is admitted as a being.
Nothing here depends on RH or asserts anything about physical reality.
-/

namespace Neoplatonic

/-! ## Positive naturals under proper divisibility -/

/-- `d` is a proper divisor of `n`: the immediate-ground relation of arithmetic. -/
def divPrior (d n : ℕ+) : Prop := (d : ℕ) ∣ (n : ℕ) ∧ d ≠ n

theorem divPrior_lt {d n : ℕ+} (h : divPrior d n) : (d : ℕ) < (n : ℕ) := by
  obtain ⟨hdvd, hne⟩ := h
  refine lt_of_le_of_ne (Nat.le_of_dvd n.pos hdvd) ?_
  intro heq
  exact hne (PNat.eq heq)

theorem divPrior_wf : WellFounded divPrior := by
  refine Subrelation.wf ?_ (measure (fun n : ℕ+ => (n : ℕ))).wf
  intro a b h
  exact divPrior_lt h

/-- The unit reaches everything in one step or none. -/
theorem one_reaches (n : ℕ+) : Reach divPrior 1 n := by
  by_cases h : n = 1
  · subst h
    exact Reach.refl 1
  · refine Reach.step (Reach.refl 1) ⟨?_, ?_⟩
    · simp
    · exact fun h1 => h h1.symm

/-- Nothing properly divides the unit. -/
theorem root_one : Root divPrior 1 := by
  rintro ⟨d, hd, hne⟩
  have h1 : (d : ℕ) ∣ 1 := by simpa using hd
  exact hne (PNat.eq (by simpa using Nat.dvd_one.mp h1))

theorem reach_mul_right (a b : ℕ+) : Reach divPrior a (a * b) := by
  by_cases hb : b = 1
  · subst hb
    simpa using Reach.refl a
  · refine Reach.step (Reach.refl a) ⟨?_, ?_⟩
    · exact ⟨(b : ℕ), by simp⟩
    · intro h
      -- older mathlib: `mul_right_eq_self.mp h`
      exact hb (mul_eq_left.mp h.symm)

theorem reach_mul_left (a b : ℕ+) : Reach divPrior b (a * b) := by
  rw [mul_comm]
  exact reach_mul_right b a

/-- Arithmetic, unit included, is a confluent ground theory.
`commonEffect` is witnessed by the product; `localCoherence` by the unit. -/
def divisibilityTheory : ConfluentGroundTheory ℕ+ where
  prior := divPrior
  wf := divPrior_wf
  commonEffect := fun a b => ⟨a * b, reach_mul_right a b, reach_mul_left a b⟩
  localCoherence := fun x y _ _ _ => ⟨1, one_reaches x, one_reaches y⟩

theorem one_is_first_principle : FirstPrinciple divPrior 1 :=
  ⟨root_one, one_reaches⟩

/-- The One of arithmetic is the number one. -/
theorem one_is_unique_first_principle :
    ∃! g : ℕ+, FirstPrinciple divPrior g :=
  confluent_unique_first_principle divisibilityTheory 1

/-- The model is not linear: `2` and `3` are incomparable immediate grounds of `6`.
(`CoherentModel.lean` makes the same point with three hand-built nodes.) -/
theorem six_has_incomparable_co_grounds :
    divPrior 2 6 ∧ divPrior 3 6 ∧ ¬ divPrior 2 3 ∧ ¬ divPrior 3 2 := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_⟩ <;>
  · rintro ⟨h, _⟩
    revert h
    decide

/-! ## The unit removed: the primes are the roots -/

/-- The beings of arithmetic with the empty product excluded. -/
abbrev NonUnit := {n : ℕ // 2 ≤ n}

def divPrior₂ (d n : NonUnit) : Prop := (d : ℕ) ∣ (n : ℕ) ∧ d ≠ n

theorem divPrior₂_of {d n : ℕ} (hd : 2 ≤ d) (hn : 2 ≤ n)
    (hdvd : d ∣ n) (hne : d ≠ n) : divPrior₂ ⟨d, hd⟩ ⟨n, hn⟩ :=
  ⟨hdvd, fun h => hne (congrArg Subtype.val h)⟩

theorem divPrior₂_wf : WellFounded divPrior₂ := by
  refine Subrelation.wf ?_ (measure (fun n : NonUnit => (n : ℕ))).wf
  intro a b h
  obtain ⟨hdvd, hne⟩ := h
  have hb := b.2
  refine lt_of_le_of_ne (Nat.le_of_dvd (by omega) hdvd) ?_
  intro heq
  exact hne (Subtype.ext heq)

/-- Roots of unitless arithmetic are exactly the primes. -/
theorem root₂_iff_prime (n : NonUnit) : Root divPrior₂ n ↔ (n : ℕ).Prime := by
  have h2 := n.2
  constructor
  · intro hroot
    rw [Nat.prime_def_minFac]
    refine ⟨h2, ?_⟩
    by_contra hne
    have hp : (Nat.minFac n).Prime := Nat.minFac_prime (by omega)
    apply hroot
    refine ⟨⟨Nat.minFac n, hp.two_le⟩, Nat.minFac_dvd n, ?_⟩
    intro h
    exact hne (congrArg Subtype.val h)
  · rintro hp ⟨d, hd, hne⟩
    have hd2 := d.2
    rcases hp.eq_one_or_self_of_dvd d hd with h1 | h
    · omega
    · exact hne (Subtype.ext h)

/-- Euclid, read as a statement about grounding: the roots are unbounded. -/
theorem roots₂_unbounded (m : ℕ) :
    ∃ p : NonUnit, m ≤ (p : ℕ) ∧ Root divPrior₂ p := by
  obtain ⟨p, hmp, hp⟩ := Nat.exists_infinite_primes m
  exact ⟨⟨p, hp.two_le⟩, hmp, (root₂_iff_prime _).mpr hp⟩

/-- Products still exist, so `commonEffect` holds without the unit. -/
def mulNU (a b : NonUnit) : NonUnit := ⟨a * b, by nlinarith [a.2, b.2]⟩

theorem reach₂_mul_right (a b : NonUnit) : Reach divPrior₂ a (mulNU a b) := by
  have ha := a.2
  have hb := b.2
  refine Reach.step (Reach.refl a) ⟨⟨(b : ℕ), rfl⟩, ?_⟩
  intro h
  have h2 : (a : ℕ) = (a : ℕ) * (b : ℕ) := congrArg Subtype.val h
  nlinarith

theorem reach₂_mul_left (a b : NonUnit) : Reach divPrior₂ b (mulNU a b) := by
  have : mulNU a b = mulNU b a := Subtype.ext (Nat.mul_comm _ _)
  rw [this]
  exact reach₂_mul_right b a

theorem commonEffect₂ :
    ∀ a b : NonUnit, ∃ z : NonUnit, Reach divPrior₂ a z ∧ Reach divPrior₂ b z :=
  fun a b => ⟨mulNU a b, reach₂_mul_right a b, reach₂_mul_left a b⟩

/-- Local coherence fails at `6`: its immediate grounds `2` and `3` are both
roots and distinct, so they have no common ancestor. This is the exact
hypothesis of `LocalConfluence.lean` that arithmetic refuses to supply. -/
theorem not_locally_coherent₂ : ¬ LocallyCoherent divPrior₂ := by
  intro lc
  obtain ⟨w, hw2, hw3⟩ := lc ⟨2, le_refl 2⟩ ⟨3, by decide⟩ ⟨6, by decide⟩
    (divPrior₂_of _ _ (by decide) (by decide))
    (divPrior₂_of _ _ (by decide) (by decide))
  have h2 : w = ⟨2, le_refl 2⟩ :=
    ancestor_of_root_eq ((root₂_iff_prime _).mpr Nat.prime_two) hw2
  have h3 : w = ⟨3, by decide⟩ :=
    ancestor_of_root_eq ((root₂_iff_prime _).mpr Nat.prime_three) hw3
  have := congrArg Subtype.val (h2.symm.trans h3)
  norm_num at this

/-- Consequently there is no first principle at all without the unit. -/
theorem no_first_principle₂ : ¬ ∃ g : NonUnit, FirstPrinciple divPrior₂ g := by
  rintro ⟨g, hg⟩
  have h2 : g = ⟨2, le_refl 2⟩ :=
    ancestor_of_root_eq ((root₂_iff_prime _).mpr Nat.prime_two) (hg.2 _)
  have h3 : g = ⟨3, by decide⟩ :=
    ancestor_of_root_eq ((root₂_iff_prime _).mpr Nat.prime_three) (hg.2 _)
  have := congrArg Subtype.val (h2.symm.trans h3)
  norm_num at this

/-! ### Coprimality is "no common ground" -/

theorem reach₂_dvd {w n : NonUnit} (h : Reach divPrior₂ w n) : (w : ℕ) ∣ n := by
  induction h with
  | refl => exact dvd_refl _
  | step _ hlast ih => exact dvd_trans ih hlast.1

theorem reach₂_of_dvd {d n : NonUnit} (h : (d : ℕ) ∣ n) : Reach divPrior₂ d n := by
  by_cases hdn : d = n
  · subst hdn
    exact Reach.refl d
  · exact Reach.step (Reach.refl d) ⟨h, hdn⟩

theorem coprime_no_common_ground {a b : NonUnit} (h : Nat.Coprime (a : ℕ) b) :
    ¬ ∃ w : NonUnit, Reach divPrior₂ w a ∧ Reach divPrior₂ w b := by
  rintro ⟨w, hwa, hwb⟩
  have hw : (w : ℕ) ∣ Nat.gcd a b := Nat.dvd_gcd (reach₂_dvd hwa) (reach₂_dvd hwb)
  rw [h.gcd_eq_one] at hw
  have := Nat.le_of_dvd one_pos hw
  have := w.2
  omega

/-- `commonPrior` for a pair, in unitless arithmetic, is exactly non-coprimality. -/
theorem common_ground_iff_not_coprime (a b : NonUnit) :
    (∃ w : NonUnit, Reach divPrior₂ w a ∧ Reach divPrior₂ w b) ↔
      ¬ Nat.Coprime (a : ℕ) b := by
  constructor
  · intro hw hc
    exact coprime_no_common_ground hc hw
  · intro hc
    have hg : 2 ≤ Nat.gcd a b := by
      have hpos : 0 < Nat.gcd a b :=
        Nat.gcd_pos_of_pos_left _ (by have := a.2; omega)
      have hne : Nat.gcd a b ≠ 1 := hc
      omega
    exact ⟨⟨Nat.gcd a b, hg⟩,
      reach₂_of_dvd (Nat.gcd_dvd_left _ _),
      reach₂_of_dvd (Nat.gcd_dvd_right _ _)⟩

/-! ## The link to `riemannZeta`

Mathlib lemmas restated under the present reading. They are the only proven
connection between `riemannZeta` and a grounding order, and they run through
divisibility, not through the zeros. -/

/-- The incidence zeta of the divisibility order, inverted by Möbius, is the
indicator of the unit. -/
theorem zeta_mul_moebius_isolates_unit :
    ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℤ) *
      (ArithmeticFunction.moebius : ArithmeticFunction ℤ) = 1 := by
  simpa using ArithmeticFunction.coe_zeta_mul_coe_moebius (R := ℤ)

theorem unit_indicator (n : ℕ) :
    (1 : ArithmeticFunction ℤ) n = if n = 1 then 1 else 0 :=
  ArithmeticFunction.one_apply

/-- For `Re s > 1`, the Riemann zeta function is the L-series of the incidence
zeta of the divisibility order. -/
theorem riemannZeta_eq_divisibility_zeta {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => ((ArithmeticFunction.zeta n : ℕ) : ℂ)) s = riemannZeta s :=
  ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs

end Neoplatonic
