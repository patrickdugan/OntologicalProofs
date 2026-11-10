import Neoplatonic.LTR.SixDimensionalLabelledContinuity
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic

/-!
# LTR-MAN-77: attained six-dimensional Connes dual suprema

Normalize each four-truth observable by subtracting its value at 00.
Under finite exact distances from 00, this puts every admissible
observable into a closed and bounded product of four complex discs.
The genuine labelled Dirac commutator norm is continuous by MAN-77's
finite-dimensional linear-map theorem.

Consequently the normalized admissible unit ball is nonempty and
compact. Every finite distance-two supremum is achieved, after
translation of any other admissible truth observable into the same
normalized compact set.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Unit-admissible four-truth observables with the 00 coordinate
fixed to zero. -/
def sixLabelledNormalizedAdmissible
    (label : Fin 6 → Fin 4) (D : SixMat) : Set (Fin 4 → ℂ) :=
  {f | f 0 = 0 ∧ ‖sixLabelledDiracComm label D f‖ ≤ 1}

/-- Finite exact distances from 00 make the normalized admissible
unit ball compact in the genuine four-complex-dimensional space. -/
theorem sixLabelled_normalizedAdmissible_compact
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hd01 : sixLabelledConnesDistance label D 0 1 = 1)
    (hd02 : sixLabelledConnesDistance label D 0 2 = 1)
    (hd03 : sixLabelledConnesDistance label D 0 3 = 2) :
    IsCompact (sixLabelledNormalizedAdmissible label D) := by
  let S := sixLabelledNormalizedAdmissible label D
  have hcont : Continuous (fun f : Fin 4 → ℂ =>
      ‖sixLabelledDiracComm label D f‖) :=
    sixLabelledDiracFourNorm_continuous label D
  have hclosed : IsClosed S := by
    change IsClosed
      ({f : Fin 4 → ℂ | f 0 = 0} ∩
        {f : Fin 4 → ℂ | ‖sixLabelledDiracComm label D f‖ ≤ 1})
    exact (isClosed_eq (by fun_prop) continuous_const).inter
      (isClosed_le hcont continuous_const)
  have hbound : ∀ f ∈ S, ∀ i : Fin 4, ‖f i‖ ≤ 2 := by
    intro f hf i
    obtain ⟨hf0, hunit⟩ := hf
    have h01 := sixLabelledConnesDistance_bounds
      label D 0 1 1 (by simp [hd01]) f hunit
    have h02 := sixLabelledConnesDistance_bounds
      label D 0 2 1 (by simp [hd02]) f hunit
    have h03 := sixLabelledConnesDistance_bounds
      label D 0 3 2 (by simp [hd03]) f hunit
    have hb1 : ‖f 1‖ ≤ (1 : ℝ) := by
      simpa [hf0] using h01
    have hb2 : ‖f 2‖ ≤ (1 : ℝ) := by
      simpa [hf0] using h02
    have hb3 : ‖f 3‖ ≤ (2 : ℝ) := by
      simpa [hf0] using h03
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

/-- Zero is always normalized and admissible. -/
theorem sixLabelled_normalizedAdmissible_nonempty
    (label : Fin 6 → Fin 4) (D : SixMat) :
    (sixLabelledNormalizedAdmissible label D).Nonempty := by
  refine ⟨0, ?_⟩
  change (0 : Fin 4 → ℂ) 0 = 0 ∧
    ‖sixLabelledDiracComm label D (0 : Fin 4 → ℂ)‖ ≤ 1
  constructor
  · rfl
  · have hz : sixLabelledDiracComm label D (0 : Fin 4 → ℂ) = 0 := by
      change (sixLabelledDiracFourLinearMap label D) 0 = 0
      exact map_zero _
    rw [hz]
    norm_num

/-- Every prescribed distance-two supremum is attained by a
genuine six-dimensional labelled Dirac admissible observable. -/
theorem sixLabelled_distanceTwo_attained
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hd01 : sixLabelledConnesDistance label D 0 1 = 1)
    (hd02 : sixLabelledConnesDistance label D 0 2 = 1)
    (hd03 : sixLabelledConnesDistance label D 0 3 = 2)
    (u v : Fin 4)
    (hduv : sixLabelledConnesDistance label D u v = 2) :
    ∃ f : sixLabelledAdmissible label D,
      ‖f.val v - f.val u‖ = 2 := by
  let S := sixLabelledNormalizedAdmissible label D
  have hc : IsCompact S :=
    sixLabelled_normalizedAdmissible_compact label D hd01 hd02 hd03
  have hn : S.Nonempty :=
    sixLabelled_normalizedAdmissible_nonempty label D
  have hobj : Continuous
      (fun f : Fin 4 → ℂ => ‖f u - f v‖) := by
    fun_prop
  obtain ⟨g, hg, hmax⟩ :=
    hc.exists_isMaxOn hn hobj.continuousOn
  have hunit : ‖sixLabelledDiracComm label D g‖ ≤ 1 := hg.2
  have hle : ‖g u - g v‖ ≤ (2 : ℝ) :=
    sixLabelledConnesDistance_bounds
      label D u v 2 (by simp [hduv]) g hunit
  have hmax_bound (f : sixLabelledAdmissible label D) :
      ‖f.val u - f.val v‖ ≤ ‖g u - g v‖ := by
    let shifted : Fin 4 → ℂ := fun i => f.val i - f.val 0
    have hshunit : ‖sixLabelledDiracComm label D shifted‖ ≤ 1 := by
      change ‖sixLabelledDiracComm label D
        (fun i => f.val i - f.val 0)‖ ≤ 1
      rw [sixLabelledDiracComm_sub_const]
      exact f.property
    have hshift : shifted ∈ S := by
      change shifted 0 = 0 ∧
        ‖sixLabelledDiracComm label D shifted‖ ≤ 1
      exact ⟨by simp [shifted], hshunit⟩
    have heq : shifted u - shifted v =
        f.val u - f.val v := by
      change (f.val u - f.val 0) - (f.val v - f.val 0) = _
      ring
    have hmaxFr : ‖shifted u - shifted v‖ ≤ ‖g u - g v‖ :=
      hmax hshift
    simpa only [heq] using hmaxFr
  let M : ℝ≥0 := ⟨‖g u - g v‖, norm_nonneg _⟩
  have hsup : sixLabelledConnesDistance label D u v ≤ (M : ℝ≥0∞) := by
    unfold sixLabelledConnesDistance
    apply iSup_le
    intro f
    have hm := hmax_bound f
    have hnn : ‖f.val u - f.val v‖₊ ≤ M := by
      apply NNReal.coe_le_coe.mp
      change ‖f.val u - f.val v‖ ≤ ‖g u - g v‖
      exact hm
    exact ENNReal.coe_le_coe.mpr hnn
  have hgeNN : (2 : ℝ≥0) ≤ M := by
    apply ENNReal.coe_le_coe.mp
    calc
      (2 : ℝ≥0∞) = sixLabelledConnesDistance label D u v := hduv.symm
      _ ≤ (M : ℝ≥0∞) := hsup
  have hge : (2 : ℝ) ≤ ‖g u - g v‖ := by
    have hh := NNReal.coe_le_coe.mpr hgeNN
    change (2 : ℝ) ≤ ‖g u - g v‖ at hh
    exact hh
  have heq : ‖g u - g v‖ = 2 := le_antisymm hle hge
  refine ⟨⟨g, hunit⟩, ?_⟩
  simpa only [norm_sub_rev] using heq

end Neoplatonic.LTR
