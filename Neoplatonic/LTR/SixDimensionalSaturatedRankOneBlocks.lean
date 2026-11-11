import Neoplatonic.LTR.SixDimensionalZeroEnergyBlocks
import Mathlib.Tactic

/-!
# LTR-MAN-86: rank-one minor certificates for saturated opposite Dirac blocks

A truth-fibre block Q_u D Q_v has entries only in rows labelled u
and columns labelled v. If either truth fibre has multiplicity one,
then any two nonzero entries share a common row or column index.

Over the complex field this support geometry forces every 2×2
minor of the full six-dimensional embedded block to vanish:

  B_ij B_kl = B_il B_kj.

With nonzero block, this is a rank-one certificate expressed entirely
as verified matrix equalities, independent of any rank API coercions.

In the eight exact-Hamming multiplicity patterns where both opposite
pair minimum fibre dimensions equal one, MAN-85/86 saturation forces
a dichotomy: one opposite block vanishes in both orientations, while
the surviving block is nonzero with all 2×2 minors zero.
-/

namespace Neoplatonic.LTR

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- A truth fibre of multiplicity one has exactly one Hilbert
coordinate, hence any two indices bearing that truth label coincide. -/
theorem sixTruthFibreMultiplicity_one_unique
    (label : Fin 6 → Fin 4) (u : Fin 4)
    (hm : truthMultiplicity label u = 1)
    (i j : Fin 6) (hi : label i = u) (hj : label j = u) :
    i = j := by
  let s : Finset (Fin 6) := Finset.univ.filter (fun k => label k = u)
  have hc : s.card = 1 := hm
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hc
  have him : i ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  have hjm : j ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  rw [hk] at him hjm
  simp only [Finset.mem_singleton] at him hjm
  exact him.trans hjm.symm

/-- Every nonzero entry of a labelled truth block lies in its
specified source row fibre and target column fibre. -/
theorem sixTruthFibreBlock_nonzero_support
    (label : Fin 6 → Fin 4) (D : SixMat)
    (u v : Fin 4) (i j : Fin 6)
    (h : sixTruthFibreBlock label D u v i j ≠ 0) :
    label i = u ∧ label j = v := by
  by_contra hc
  have hz : sixTruthFibreBlock label D u v i j = 0 := by
    rw [sixTruthFibreBlock_entry]
    simp [hc]
  exact h hz

/-- With minimum endpoint fibre dimension one, every two
nonzero entries of the whole truth block share their row or
column index. -/
theorem sixTruthFibreBlock_minOne_nonzero_share_index
    (label : Fin 6 → Fin 4) (D : SixMat)
    (u v : Fin 4)
    (hmin : min (truthMultiplicity label u)
      (truthMultiplicity label v) = 1)
    (i k j l : Fin 6)
    (hij : sixTruthFibreBlock label D u v i j ≠ 0)
    (hkl : sixTruthFibreBlock label D u v k l ≠ 0) :
    i = k ∨ j = l := by
  obtain ⟨hi, hj⟩ :=
    sixTruthFibreBlock_nonzero_support label D u v i j hij
  obtain ⟨hk, hl⟩ :=
    sixTruthFibreBlock_nonzero_support label D u v k l hkl
  have hcase : truthMultiplicity label u = 1 ∨
      truthMultiplicity label v = 1 := by
    omega
  rcases hcase with hu | hv
  · exact Or.inl (sixTruthFibreMultiplicity_one_unique
      label u hu i k hi hk)
  · exact Or.inr (sixTruthFibreMultiplicity_one_unique
      label v hv j l hj hl)

/-- Entries with distinct row and column indices cannot both
be nonzero in a truth-fibre block with a one-dimensional endpoint. -/
theorem sixTruthFibreBlock_minOne_disjoint_product_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (u v : Fin 4)
    (hmin : min (truthMultiplicity label u)
      (truthMultiplicity label v) = 1)
    (i k j l : Fin 6) (hik : i ≠ k) (hjl : j ≠ l) :
    sixTruthFibreBlock label D u v i j *
      sixTruthFibreBlock label D u v k l = 0 := by
  by_cases hz : sixTruthFibreBlock label D u v i j = 0
  · simp [hz]
  · have hz' : sixTruthFibreBlock label D u v k l = 0 := by
      by_contra hn
      rcases sixTruthFibreBlock_minOne_nonzero_share_index
        label D u v hmin i k j l hz hn with heq | heq
      · exact hik heq
      · exact hjl heq
    simp [hz']

/-- Every 2×2 minor of a minimum-one-endpoint truth-fibre block
vanishes: a complete rank-at-most-one matrix certificate. -/
theorem sixTruthFibreBlock_minOne_allTwoByTwoMinors_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (u v : Fin 4)
    (hmin : min (truthMultiplicity label u)
      (truthMultiplicity label v) = 1)
    (i k j l : Fin 6) :
    sixTruthFibreBlock label D u v i j *
      sixTruthFibreBlock label D u v k l =
    sixTruthFibreBlock label D u v i l *
      sixTruthFibreBlock label D u v k j := by
  by_cases hik : i = k
  · subst k
    ring
  by_cases hjl : j = l
  · subst l
    ring
  have hleft :=
    sixTruthFibreBlock_minOne_disjoint_product_zero
      label D u v hmin i k j l hik hjl
  have hright :=
    sixTruthFibreBlock_minOne_disjoint_product_zero
      label D u v hmin i k l j hik hjl.symm
  rw [hleft, hright]

/-- The signed-quartet saturation geometry produces a concrete
rank-one support dichotomy: exactly one opposite Dirac block
survives, and all its 2×2 minors vanish. -/
theorem sixLabelled_exactHamming_minOne_saturation_rankOneDichotomy
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (hmin03 : min (truthMultiplicity label 0)
      (truthMultiplicity label 3) = 1)
    (hmin12 : min (truthMultiplicity label 1)
      (truthMultiplicity label 2) = 1)
    (hsat : |sixTruthFibreBlockEnergy label D 0 3 -
      sixTruthFibreBlockEnergy label D 1 2| = (1 / 4 : ℝ)) :
    (sixTruthFibreBlock label D 0 3 = 0 ∧
       sixTruthFibreBlock label D 3 0 = 0 ∧
       sixTruthFibreBlock label D 1 2 ≠ 0 ∧
       ∀ i k j l : Fin 6,
         sixTruthFibreBlock label D 1 2 i j *
           sixTruthFibreBlock label D 1 2 k l =
         sixTruthFibreBlock label D 1 2 i l *
           sixTruthFibreBlock label D 1 2 k j) ∨
    (sixTruthFibreBlock label D 1 2 = 0 ∧
       sixTruthFibreBlock label D 2 1 = 0 ∧
       sixTruthFibreBlock label D 0 3 ≠ 0 ∧
       ∀ i k j l : Fin 6,
         sixTruthFibreBlock label D 0 3 i j *
           sixTruthFibreBlock label D 0 3 k l =
         sixTruthFibreBlock label D 0 3 i l *
           sixTruthFibreBlock label D 0 3 k j) := by
  rcases sixLabelled_exactHamming_minOne_saturation_blocksExclusive
    label D hD hham hmin03 hmin12 hsat with
    ⟨h03, h30, _, hn12⟩ | ⟨h12, h21, _, hn03⟩
  · exact Or.inl ⟨h03, h30, hn12,
      fun i k j l =>
        sixTruthFibreBlock_minOne_allTwoByTwoMinors_zero
          label D 1 2 hmin12 i k j l⟩
  · exact Or.inr ⟨h12, h21, hn03,
      fun i k j l =>
        sixTruthFibreBlock_minOne_allTwoByTwoMinors_zero
          label D 0 3 hmin03 i k j l⟩

end Neoplatonic.LTR
