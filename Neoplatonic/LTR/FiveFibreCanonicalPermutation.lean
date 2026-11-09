import Neoplatonic.LTR.FiveFibreChartPermutation
import Mathlib.Tactic

/-!
# LTR-MAN-40: arbitrary duplicated truth fibres admit a standard chart

MAN-38 classifies the unique doubled truth atom of every faithful
five-dimensional diagonal truth representation. MAN-39 supplies a
permutation whenever the finite truth fibres match in cardinality.

The standard chart for a doubled atom v assigns Hilbert coordinates
0,1,2,3 to truth atoms 0,1,2,3, with coordinate 4 another copy of v.
Its four fibre counts match those of every faithful diagonal labeling
with duplicated atom v. Consequently there is an actual basis-coordinate
permutation transforming every faithful label into this standard chart.

For v = 00 the standard chart is the canonical one used by MAN-37.
Boolean-square vertex relabeling and invariance of the analytic
Connes dual metric under this permutation are separate obligations.
-/

namespace Neoplatonic.LTR

/-- Standard label for five Hilbert coordinates and an arbitrary
doubled truth atom. -/
def fiveFibreStandardLabel (v : Fin 4) (i : Fin 5) : Fin 4 :=
  if h : i.val < 4 then ⟨i.val, h⟩ else v

/-- Its fibre multiplicities have the universal (2,1,1,1) pattern. -/
theorem fiveFibreStandardLabel_multiplicity (v w : Fin 4) :
    fiveFibreTruthMultiplicity (fiveFibreStandardLabel v) w =
      if w = v then 2 else 1 := by
  fin_cases v <;> fin_cases w <;> decide

/-- The doubled-00 standard chart agrees with the canonical chart. -/
theorem fiveFibreStandardLabel_zero :
    fiveFibreStandardLabel 0 = fiveFibreCanonicalLabel := by
  funext i
  fin_cases i <;> decide

/-- Every faithful diagonal five-dimensional truth representation
admits a basis permutation into a standard chart with its duplicated
atom at coordinate four and at its corresponding coordinate in 0..3. -/
theorem fiveFibreFaithful_exists_standardPermutation
    (label : Fin 5 → Fin 4)
    (hsurj : Function.Surjective label) :
    ∃ (v : Fin 4) (σ : Equiv.Perm (Fin 5)),
      ∀ i : Fin 5, label (σ i) = fiveFibreStandardLabel v i := by
  classical
  obtain ⟨v, hv, hother⟩ :=
    fiveFibreFaithful_uniqueDouble label hsurj
  have hcounts (w : Fin 4) :
      fiveFibreTruthMultiplicity (fiveFibreStandardLabel v) w =
        fiveFibreTruthMultiplicity label w := by
    rw [fiveFibreStandardLabel_multiplicity]
    by_cases hw : w = v
    · subst w
      simpa using hv.symm
    · simp [hw, hother w hw]
  obtain ⟨σ, hσ⟩ :=
    fiveFibre_equalMultiplicities_permutation
      (fiveFibreStandardLabel v) label hcounts
  exact ⟨v, σ, hσ⟩

end Neoplatonic.LTR
