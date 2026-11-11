import Neoplatonic.LTR.SixDimensionalExactHammingPauliSaturation
import Mathlib.Tactic

/-!
# LTR-MAN-86: zero squared Dirac energy kills the whole opposite truth block

The MAN-81 energy of a labelled Dirac truth block is a finite sum of
nonnegative squared complex entry norms. It vanishes exactly when
the entire six-dimensional embedded block is the zero matrix.

This applies to arbitrary complex Dirac matrices, including
multi-coordinate truth fibres; no Hermiticity assumption is
needed for the equivalence itself.

When D is Hermitian, zero energy in one orientation also kills the
conjugate-transposed reverse block and every underlying Dirac entry
between the two labelled truth atoms.

Combined with MAN-85's half-unit Pauli saturation theorem, all
six-dimensional exact-Hamming representations whose two opposite
truth-pair minima equal one exhibit an exclusive pair:
exactly one opposite block is zero, and the surviving block has
nonzero squared energy 1/4.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- The sum of squares of all complex matrix entries is zero
if and only if the entire finite matrix is zero. -/
theorem sixMatrix_squaredEntryEnergy_eq_zero_iff
    (M : SixMat) :
    (∑ j : Fin 6, ∑ i : Fin 6, ‖M i j‖ ^ 2) = 0 ↔ M = 0 := by
  constructor
  · intro hsum
    have hnonneg (j : Fin 6) :
        0 ≤ ∑ i : Fin 6, ‖M i j‖ ^ 2 := by
      apply Finset.sum_nonneg
      intro i hi
      exact sq_nonneg _
    have hcol (j : Fin 6) :
        (∑ i : Fin 6, ‖M i j‖ ^ 2) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj => hnonneg j)).mp hsum j (Finset.mem_univ j)
    ext i j
    have hterm : ‖M i j‖ ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun k hk => sq_nonneg (‖M k j‖))).mp
        (hcol j) i (Finset.mem_univ i)
    have hn : ‖M i j‖ = 0 := by
      nlinarith [norm_nonneg (M i j)]
    exact norm_eq_zero.mp hn
  · intro h
    rw [h]
    simp

/-- A complete truth-fibre block has zero squared Dirac coupling
energy precisely when its entire matrix vanishes. -/
theorem sixTruthFibreBlockEnergy_zero_iff_block_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (u v : Fin 4) :
    sixTruthFibreBlockEnergy label D u v = 0 ↔
      sixTruthFibreBlock label D u v = 0 := by
  unfold sixTruthFibreBlockEnergy
  exact sixMatrix_squaredEntryEnergy_eq_zero_iff
    (sixTruthFibreBlock label D u v)

/-- Zero block energy also means that *every* original Dirac entry
between the two specified truth fibres vanishes. -/
theorem sixTruthFibreBlockEnergy_zero_iff_couplings_zero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (u v : Fin 4) :
    sixTruthFibreBlockEnergy label D u v = 0 ↔
      ∀ i j : Fin 6, label i = u → label j = v → D i j = 0 := by
  constructor
  · intro hz i j hi hj
    have hblock :=
      (sixTruthFibreBlockEnergy_zero_iff_block_zero
        label D u v).mp hz
    have hentry := congrArg (fun M : SixMat => M i j) hblock
    rw [sixTruthFibreBlock_entry] at hentry
    simpa [hi, hj] using hentry
  · intro hzero
    apply (sixTruthFibreBlockEnergy_zero_iff_block_zero
      label D u v).mpr
    ext i j
    rw [sixTruthFibreBlock_entry]
    by_cases hi : label i = u
    · by_cases hj : label j = v
      · simp [hi, hj, hzero i j hi hj]
      · simp [hi, hj]
    · simp [hi]

/-- For a Hermitian Dirac operator, a vanished oriented truth block
kills the reverse block by conjugate transpose. -/
theorem sixTruthFibreBlock_zero_reverse
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hD : ∀ i j, D i j = star (D j i))
    (u v : Fin 4)
    (hzero : sixTruthFibreBlock label D u v = 0) :
    sixTruthFibreBlock label D v u = 0 := by
  rw [← sixTruthFibreBlock_conjTranspose label D hD u v,
    hzero]
  simp

/-- If the squared energy is strictly positive, the entire truth
block is nonzero. This will certify the surviving saturation block. -/
theorem sixTruthFibreBlockEnergy_pos_implies_nonzero
    (label : Fin 6 → Fin 4) (D : SixMat)
    (u v : Fin 4)
    (hpos : 0 < sixTruthFibreBlockEnergy label D u v) :
    sixTruthFibreBlock label D u v ≠ 0 := by
  intro hz
  have he := (sixTruthFibreBlockEnergy_zero_iff_block_zero
    label D u v).mpr hz
  linarith

/-- Under exact-Hamming metric saturation in the min-one fibre
cases, one entire opposite-corner Dirac block and its reverse vanish,
while the surviving opposite block has real squared energy 1/4
and is nonzero. -/
theorem sixLabelled_exactHamming_minOne_saturation_blocksExclusive
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
       sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ) ∧
       sixTruthFibreBlock label D 1 2 ≠ 0) ∨
    (sixTruthFibreBlock label D 1 2 = 0 ∧
       sixTruthFibreBlock label D 2 1 = 0 ∧
       sixTruthFibreBlockEnergy label D 0 3 = (1 / 4 : ℝ) ∧
       sixTruthFibreBlock label D 0 3 ≠ 0) := by
  rcases sixLabelled_exactHamming_minOne_saturation_energyExclusive
    label D hD hham hmin03 hmin12 hsat with
    ⟨h03, h12⟩ | ⟨h03, h12⟩
  · right
    have hz := (sixTruthFibreBlockEnergy_zero_iff_block_zero
      label D 1 2).mp h12
    have hrev := sixTruthFibreBlock_zero_reverse label D hD 1 2 hz
    refine ⟨hz, hrev, h03, ?_⟩
    exact sixTruthFibreBlockEnergy_pos_implies_nonzero label D 0 3
      (by rw [h03]; norm_num)
  · left
    have hz := (sixTruthFibreBlockEnergy_zero_iff_block_zero
      label D 0 3).mp h03
    have hrev := sixTruthFibreBlock_zero_reverse label D hD 0 3 hz
    refine ⟨hz, hrev, h12, ?_⟩
    exact sixTruthFibreBlockEnergy_pos_implies_nonzero label D 1 2
      (by rw [h12]; norm_num)

/-- At saturation, every Dirac matrix entry on one of the two
opposite truth diagonals vanishes, including both orientations. -/
theorem sixLabelled_exactHamming_minOne_saturation_oppositeCouplingsZero
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
    (∀ i j : Fin 6, label i = 0 → label j = 3 → D i j = 0) ∨
    (∀ i j : Fin 6, label i = 1 → label j = 2 → D i j = 0) := by
  rcases sixLabelled_exactHamming_minOne_saturation_blocksExclusive
    label D hD hham hmin03 hmin12 hsat with h | h
  · right
    exact (sixTruthFibreBlockEnergy_zero_iff_couplings_zero
      label D 1 2).mp
        ((sixTruthFibreBlockEnergy_zero_iff_block_zero
          label D 1 2).mpr h.1)
  · left
    exact (sixTruthFibreBlockEnergy_zero_iff_couplings_zero
      label D 0 3).mp
        ((sixTruthFibreBlockEnergy_zero_iff_block_zero
          label D 0 3).mpr h.1)

end Neoplatonic.LTR
