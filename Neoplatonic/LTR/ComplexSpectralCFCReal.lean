import Neoplatonic.LTR.ComplexSpectralDyadicLimits
import Mathlib.Topology.CompactOpen
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Real continuous-functional-calculus powers of the Dirac resolvent

The scalar power function is jointly continuous when its exponent is
positive, including at spectral value zero. Currying on the compact
spectrum and applying the continuous CFC homomorphism therefore gives
operator-norm continuity in the positive exponent.

Positive upper dyadic approximants then identify the CFC power with the
concrete spectral-power operator for every positive real exponent.
-/

namespace Neoplatonic.LTR

open scoped lp

local instance :
    NonUnitalClosedEmbeddingContinuousFunctionalCalculus ℂ
      (ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert)
      IsStarNormal :=
  IsStarNormal.instNonUnitalContinuousFunctionalCalculus

local instance :
    NonUnitalContinuousFunctionalCalculus ℝ
      (ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert)
      IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

local instance :
    ContinuousFunctionalCalculus ℂ
      (ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert)
      IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus

local instance :
    ContinuousFunctionalCalculus ℝ
      (ComplexDiracBlockHilbert →L[ℂ] ComplexDiracBlockHilbert)
      IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus

/-- Genuine CFC powers of the full Hilbert resolvent are continuous
in operator norm on the positive real exponent half-line. -/
theorem chosenComplexSquaredResolvent_CFC_rpow_continuousOn
    (scale : ℕ → ℝ) :
    ContinuousOn (fun p : ℝ =>
      CFC.rpow (chosenComplexSquaredResolventCLM scale) (p / 2))
      (Set.Ioi 0) := by
  let R := chosenComplexSquaredResolventCLM scale
  have hR : (0 : ComplexDiracBlockHilbert →L[ℂ]
      ComplexDiracBlockHilbert) ≤ R := by
    simpa only [R, ContinuousLinearMap.le_def, sub_zero] using
      (chosenComplexSquaredResolvent_isPositive scale)
  let F : Set.Ioi (0 : ℝ) → C(spectrum ℝ R, ℝ) :=
    fun p => ⟨fun x => (x : ℝ) ^ ((p : ℝ) / 2),
      (Real.continuous_rpow_const
        (by linarith [p.property] : 0 ≤ (p : ℝ) / 2)).comp
        continuous_subtype_val⟩
  have hF : Continuous F := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hx : Continuous
        (fun z : Set.Ioi (0 : ℝ) × spectrum ℝ R => (z.2 : ℝ)) :=
      continuous_subtype_val.comp continuous_snd
    have hp : Continuous
        (fun z : Set.Ioi (0 : ℝ) × spectrum ℝ R => (z.1 : ℝ) / 2) :=
      (continuous_subtype_val.comp continuous_fst).div_const 2
    exact hx.rpow hp (fun z => Or.inr (by linarith [z.1.property]))
  have hc : Continuous (fun p : Set.Ioi (0 : ℝ) =>
      cfcHom (R := ℝ) hR.isSelfAdjoint (F p)) :=
    (cfcHom_continuous hR.isSelfAdjoint).comp hF
  apply continuousOn_iff_continuous_domRestrict.mpr
  change Continuous (fun p : Set.Ioi (0 : ℝ) => CFC.rpow R ((p : ℝ) / 2))
  convert hc using 1
  funext p
  rw [CFC.rpow_eq_pow, CFC.rpow_eq_cfc_real hR,
    cfc_apply (fun x : ℝ => x ^ ((p : ℝ) / 2)) R hR.isSelfAdjoint
      (Real.continuous_rpow_const
        (by linarith [p.property] : 0 ≤ (p : ℝ) / 2)).continuousOn]

/-- The mesh of the positive dyadic exponents tends to zero. -/
theorem complexSpectralDyadicExponent_tendsto_zero :
    Filter.Tendsto complexSpectralDyadicExponent Filter.atTop (nhds 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul 2
  have heq : complexSpectralDyadicExponent =
      (fun n : ℕ => 2 * (1 / 2 : ℝ) ^ n) := by
    funext n
    rw [complexSpectralDyadicExponent_eq, one_div_pow]
    ring
  simpa only [heq, mul_zero] using h

/-- Every positive exponent admits positive dyadic approximants.
The chosen numerator is one more than the natural floor, so the
approximation error lies between zero and one dyadic mesh width. -/
theorem exists_complexSpectralDyadicRational_tendsto
    (p : ℝ) (hp : 0 < p) :
    ∃ m : ℕ → ℕ,
      Filter.Tendsto (fun n : ℕ =>
        complexSpectralDyadicExponent n * (Nat.succ (m n) : ℝ))
        Filter.atTop (nhds p) := by
  let m : ℕ → ℕ := fun n => ⌊p / complexSpectralDyadicExponent n⌋₊
  refine ⟨m, ?_⟩
  have hb : ∀ n : ℕ,
      0 ≤ complexSpectralDyadicExponent n * (Nat.succ (m n) : ℝ) - p ∧
      complexSpectralDyadicExponent n * (Nat.succ (m n) : ℝ) - p ≤
        complexSpectralDyadicExponent n := by
    intro n
    have hd := complexSpectralDyadicExponent_pos n
    have hl : p / complexSpectralDyadicExponent n <
        (Nat.succ (m n) : ℝ) := by
      simpa only [m, Nat.cast_succ] using
        (Nat.lt_floor_add_one (p / complexSpectralDyadicExponent n))
    have hl' := (div_lt_iff₀ hd).mp hl
    have hu : (m n : ℝ) ≤ p / complexSpectralDyadicExponent n :=
      Nat.floor_le (div_nonneg hp.le hd.le)
    have hu' := (le_div_iff₀ hd).mp hu
    constructor
    · nlinarith
    · push_cast
      nlinarith
  have hlim : Filter.Tendsto (fun n : ℕ =>
      complexSpectralDyadicExponent n * (Nat.succ (m n) : ℝ) - p)
      Filter.atTop (nhds 0) :=
    squeeze_zero (fun n => (hb n).1) (fun n => (hb n).2)
      complexSpectralDyadicExponent_tendsto_zero
  simpa only [sub_add_cancel, zero_add] using hlim.add_const p

/-- Every positive real spectral power of the actual infinite Hilbert
Dirac operator is the corresponding genuine Mathlib CFC power of its
squared resolvent. -/
theorem chosenComplexSpectralPower_eq_CFC_rpow
    (scale : ℕ → ℝ) (p : ℝ) (hp : 0 < p) :
    chosenComplexSpectralPowerCLM scale p hp =
      CFC.rpow (chosenComplexSquaredResolventCLM scale) (p / 2) := by
  obtain ⟨m, hm⟩ := exists_complexSpectralDyadicRational_tendsto p hp
  have hc : ContinuousAt (fun q : ℝ =>
      CFC.rpow (chosenComplexSquaredResolventCLM scale) (q / 2)) p :=
    (chosenComplexSquaredResolvent_CFC_rpow_continuousOn scale p hp).continuousAt
      (isOpen_Ioi.mem_nhds hp)
  have hlim : Filter.Tendsto (fun n : ℕ =>
      CFC.rpow (chosenComplexSquaredResolventCLM scale)
        (((1 / 2 : ℝ) ^ n) * (Nat.succ (m n) : ℝ)))
      Filter.atTop
      (nhds (CFC.rpow (chosenComplexSquaredResolventCLM scale) (p / 2))) := by
    convert hc.tendsto.comp hm using 1
    funext n
    congr 1
    rw [complexSpectralDyadicExponent_eq, one_div_pow]
    ring
  exact tendsto_nhds_unique
    (chosenComplexSpectralDyadicRational_CFC_tendsto scale p hp id m hm) hlim

end Neoplatonic.LTR
