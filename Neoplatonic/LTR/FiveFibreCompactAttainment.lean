import Neoplatonic.LTR.FiveFibreAttainedHammingWitnesses
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-!
# LTR-MAN-33: compactness and attainment of normalized Connes witnesses

A finite Hamming distance bounds every coordinate of an admissible
observable after its value at the first vertex is translated to zero.
Thus normalized admissible observables lie in a finite product of
closed complex discs. Their defining fibre and commutator conditions
are closed whenever the commutator seminorm is continuous.

The compact set admits a maximum of every continuous pairwise
observable difference. The resulting maximizer attains any prescribed
finite Connes dual supremum.

The continuity of the finite-dimensional Dirac commutator norm is an
explicit premise of these theorems. Supplying it from finite-dimensional
linear-map continuity is the remaining local analytic bridge.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

/-- The represented observable with its 00 truth value fixed to zero. -/
def fiveFibreSquareNormalizedAdmissible
    (D : Matrix (Fin 5) (Fin 5) ℂ) : Set (Fin 4 → ℂ) :=
  {f | f 0 = 0 ∧
    ‖fiveFibreSquareDiracComm D (fiveFibreSquareLift f)‖ ≤ 1}

/-- The lift agrees with each of the four underlying truth values. -/
theorem fiveFibreSquareLift_castSucc (f : Fin 4 → ℂ)
    (i : Fin 4) :
    fiveFibreSquareLift f i.castSucc = f i := by
  fin_cases i <;> simp [fiveFibreSquareLift]

/-- Exact finite distances from 00 make the normalized closed
commutator unit ball compact. All four coordinate radii are ≤2. -/
theorem fiveFibreSquare_normalizedAdmissible_compact
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hd01 : fiveFibreSquareConnesDualDistance D 0 1 = 1)
    (hd02 : fiveFibreSquareConnesDualDistance D 0 2 = 1)
    (hd03 : fiveFibreSquareConnesDualDistance D 0 3 = 2)
    (hcont : Continuous (fun f : Fin 4 → ℂ =>
      ‖fiveFibreSquareDiracComm D (fiveFibreSquareLift f)‖)) :
    IsCompact (fiveFibreSquareNormalizedAdmissible D) := by
  let S := fiveFibreSquareNormalizedAdmissible D
  have hclosed : IsClosed S := by
    change IsClosed
      ({f : Fin 4 → ℂ | f 0 = 0} ∩
        {f : Fin 4 → ℂ |
          ‖fiveFibreSquareDiracComm D (fiveFibreSquareLift f)‖ ≤ 1})
    exact (isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_le hcont continuous_const)
  have hbound : ∀ f ∈ S, ∀ i : Fin 4, ‖f i‖ ≤ 2 := by
    intro f hf i
    obtain ⟨hf0, hunit⟩ := hf
    have hdup : fiveFibreSquareLift f 4 =
        fiveFibreSquareLift f 0 := by
      simp [fiveFibreSquareLift]
    have h01 := fiveFibreSquareConnesDualDistance_bounds D 0 1 1
      (by simp [hd01]) (fiveFibreSquareLift f) hdup hunit
    have h02 := fiveFibreSquareConnesDualDistance_bounds D 0 2 1
      (by simp [hd02]) (fiveFibreSquareLift f) hdup hunit
    have h03 := fiveFibreSquareConnesDualDistance_bounds D 0 3 2
      (by simp [hd03]) (fiveFibreSquareLift f) hdup hunit
    have hb1 : ‖f 1‖ ≤ (1 : ℝ) := by
      simpa [fiveFibreSquareLift, hf0] using h01
    have hb2 : ‖f 2‖ ≤ (1 : ℝ) := by
      simpa [fiveFibreSquareLift, hf0] using h02
    have hb3 : ‖f 3‖ ≤ (2 : ℝ) := by
      simpa [fiveFibreSquareLift, hf0] using h03
    fin_cases i
    · simp [hf0]
    · exact hb1.trans (by norm_num)
    · exact hb2.trans (by norm_num)
    · exact hb3
  let K : Set (Fin 4 → ℂ) :=
    {f | ∀ i : Fin 4, f i ∈ Metric.closedBall (0 : ℂ) 2}
  have hK : IsCompact K := by
    change IsCompact
      {f : Fin 4 → ℂ | ∀ i, f i ∈ Metric.closedBall (0 : ℂ) 2}
    exact isCompact_pi_infinite (fun _ => isCompact_closedBall _ _)
  have hsub : S ⊆ K := by
    intro f hf i
    change dist (f i) (0 : ℂ) ≤ 2
    simpa only [dist_zero_right] using hbound f hf i
  exact hK.of_isClosed_subset hclosed hsub

/-- Zero is a normalized admissible observable for every Dirac
matrix; the normalized compact set is nonempty. -/
theorem fiveFibreSquare_normalizedAdmissible_nonempty
    (D : Matrix (Fin 5) (Fin 5) ℂ) :
    (fiveFibreSquareNormalizedAdmissible D).Nonempty := by
  refine ⟨0, ?_⟩
  have hlift : fiveFibreSquareLift (0 : Fin 4 → ℂ) = 0 := by
    funext i
    fin_cases i <;> simp [fiveFibreSquareLift]
  change (0 : Fin 4 → ℂ) 0 = 0 ∧
    ‖fiveFibreSquareDiracComm D
      (fiveFibreSquareLift (0 : Fin 4 → ℂ))‖ ≤ 1
  constructor
  · rfl
  · rw [hlift]
    simp [fiveFibreSquareDiracComm]

/-- A finite exact Connes dual distance is attained by an actual
admissible observable, provided the finite commutator norm is
continuous. The source is the four-dimensional normalized truth
function space, and the target is the original five-coordinate
faithful Hilbert representation. -/
theorem fiveFibreSquare_distanceTwo_attained_of_continuous
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hd01 : fiveFibreSquareConnesDualDistance D 0 1 = 1)
    (hd02 : fiveFibreSquareConnesDualDistance D 0 2 = 1)
    (hd03 : fiveFibreSquareConnesDualDistance D 0 3 = 2)
    (u v : Fin 4)
    (hduv : fiveFibreSquareConnesDualDistance D
      u.castSucc v.castSucc = 2)
    (hcont : Continuous (fun f : Fin 4 → ℂ =>
      ‖fiveFibreSquareDiracComm D (fiveFibreSquareLift f)‖)) :
    ∃ f : fiveFibreSquareAdmissible D,
      ‖f.val v.castSucc - f.val u.castSucc‖ = 2 := by
  let S := fiveFibreSquareNormalizedAdmissible D
  have hc : IsCompact S :=
    fiveFibreSquare_normalizedAdmissible_compact D
      hd01 hd02 hd03 hcont
  have hn : S.Nonempty :=
    fiveFibreSquare_normalizedAdmissible_nonempty D
  have hobj : Continuous
      (fun f : Fin 4 → ℂ => ‖f u - f v‖) := by
    fun_prop
  obtain ⟨g, hg, hmax⟩ :=
    hc.exists_isMaxOn hn hobj.continuousOn
  have hdup : fiveFibreSquareLift g 4 =
      fiveFibreSquareLift g 0 := by
    simp [fiveFibreSquareLift]
  have hunit : ‖fiveFibreSquareDiracComm D
      (fiveFibreSquareLift g)‖ ≤ 1 := hg.2
  have hle : ‖g u - g v‖ ≤ (2 : ℝ) := by
    have h := fiveFibreSquareConnesDualDistance_bounds D
      u.castSucc v.castSucc 2 (by simp [hduv])
      (fiveFibreSquareLift g) hdup hunit
    simpa only [fiveFibreSquareLift_castSucc] using h
  have hmax_bound (f : fiveFibreSquareAdmissible D) :
      ‖f.val u.castSucc - f.val v.castSucc‖ ≤ ‖g u - g v‖ := by
    let shifted : Fin 5 → ℂ := fun i => f.val i - f.val 0
    have hshdup : shifted 4 = shifted 0 := by
      simp [shifted, f.property.1]
    have hshunit : ‖fiveFibreSquareDiracComm D shifted‖ ≤ 1 := by
      change ‖fiveFibreSquareDiracComm D
        (fun i => f.val i - f.val 0)‖ ≤ 1
      rw [fiveFibreSquareDiracComm_sub_const]
      exact f.property.2
    let fr : Fin 4 → ℂ := fiveFibreSquareRestrict shifted
    have hfr : fr ∈ S := by
      change fr 0 = 0 ∧
        ‖fiveFibreSquareDiracComm D
          (fiveFibreSquareLift fr)‖ ≤ 1
      constructor
      · simp [fr, shifted, fiveFibreSquareRestrict]
      · rw [fiveFibreSquareLift_restrict shifted hshdup]
        exact hshunit
    have heq : fr u - fr v =
        f.val u.castSucc - f.val v.castSucc := by
      change (f.val u.castSucc - f.val 0) -
        (f.val v.castSucc - f.val 0) = _
      ring
    simpa only [heq] using hmax fr hfr
  have hsup : fiveFibreSquareConnesDualDistance D
      u.castSucc v.castSucc ≤
      ((⟨‖g u - g v‖, norm_nonneg _⟩ : ℝ≥0) : ℝ≥0∞) := by
    unfold fiveFibreSquareConnesDualDistance
    apply iSup_le
    intro f
    have hm := hmax_bound f
    have hnn : ‖f.val u.castSucc - f.val v.castSucc‖₊ ≤
        (⟨‖g u - g v‖, norm_nonneg _⟩ : ℝ≥0) := by
      apply NNReal.coe_le_coe.mp
      simpa only [coe_nnnorm] using hm
    exact ENNReal.coe_le_coe.mpr hnn
  have hgeNN : (2 : ℝ≥0) ≤
      (⟨‖g u - g v‖, norm_nonneg _⟩ : ℝ≥0) := by
    apply ENNReal.coe_le_coe.mp
    simpa [hduv] using hsup
  have hge : (2 : ℝ) ≤ ‖g u - g v‖ := by
    simpa using (NNReal.coe_le_coe.mpr hgeNN)
  have heq : ‖g u - g v‖ = 2 := le_antisymm hle hge
  refine ⟨⟨fiveFibreSquareLift g, ⟨hdup, hunit⟩⟩, ?_⟩
  simpa only [fiveFibreSquareLift_castSucc, norm_sub_rev] using heq

end Neoplatonic.LTR
