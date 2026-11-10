import Neoplatonic.LTR.FiveFibreLabelledMetricTransport
import Neoplatonic.LTR.FiveFibreTruthTranslations
import Mathlib.Tactic

/-!
# LTR-MAN-45: faithful diagonal five-dimensional exact Hamming no-go

For every surjective truth labeling Fin 5 → Fin 4 and every Hermitian
Dirac matrix, the actual labelled Connes dual distances cannot equal
all six two-bit Hamming distances.

MAN-40 supplies a Boolean-square translation and a Hilbert-coordinate
permutation taking the labeling to the canonical doubled-00 chart.
MAN-41 and MAN-42 preserve the genuine Hilbert operator norm and its
extended-real Connes dual supremum under those transformations.
MAN-44 identifies the labelled canonical supremum with the original
five-coordinate metric, allowing MAN-37's spectral obstruction to apply.

The diagonal representation hypothesis remains explicit here.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

/-- A faithful diagonal representation of the two-bit truth algebra on
five complex Hilbert coordinates cannot reproduce every Hamming
distance as its genuine Connes dual distance. -/
theorem fiveFibreFaithfulDiagonal_exactHamming_noGo
    (label : Fin 5 → Fin 4)
    (hsurj : Function.Surjective label)
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u w : Fin 4,
      fiveFibreLabelledConnesDistance label D u w =
        (twoBitSquareHamming u w : ℝ≥0∞)) :
    False := by
  obtain ⟨v, σ, _, hchart⟩ :=
    fiveFibre_faithful_allLabels_chart label hsurj
  let τ : Fin 4 ≃ Fin 4 := twoBitSquareTranslation v
  let normLabel : Fin 5 → Fin 4 := fun i => τ (label i)
  let D' : Matrix (Fin 5) (Fin 5) ℂ :=
    Matrix.reindex σ.symm σ.symm D

  have hcanonicalLabel :
      (fun i : Fin 5 => normLabel (σ i)) = fiveFibreCanonicalLabel := by
    funext i
    exact hchart i

  have hreindex (u w : Fin 4) :
      fiveFibreLabelledConnesDistance fiveFibreCanonicalLabel D' (τ u) (τ w) =
        fiveFibreLabelledConnesDistance normLabel D (τ u) (τ w) := by
    have h := fiveFibreLabelledConnesDistance_reindex
      σ.symm normLabel D (τ u) (τ w)
    have hlabel :
        (fun i : Fin 5 => normLabel ((σ.symm).symm i)) =
          fiveFibreCanonicalLabel := by
      simpa only [Equiv.symm_symm] using hcanonicalLabel
    simpa only [hlabel] using h

  have htranslation (u w : Fin 4) :
      fiveFibreLabelledConnesDistance normLabel D (τ u) (τ w) =
        fiveFibreLabelledConnesDistance label D u w := by
    change fiveFibreLabelledConnesDistance (τ ∘ label) D (τ u) (τ w) =
      fiveFibreLabelledConnesDistance label D u w
    exact fiveFibreLabelledConnesDistance_truthEquiv τ D label u w

  have hcovariance (u w : Fin 4) :
      fiveFibreLabelledConnesDistance fiveFibreCanonicalLabel D' (τ u) (τ w) =
        fiveFibreLabelledConnesDistance label D u w :=
    (hreindex u w).trans (htranslation u w)

  have hcanonicalHamming (u w : Fin 4) :
      fiveFibreLabelledConnesDistance fiveFibreCanonicalLabel D' u w =
        (twoBitSquareHamming u w : ℝ≥0∞) := by
    have hdist := hcovariance (τ.symm u) (τ.symm w)
    have hHamming :
        (twoBitSquareHamming (τ.symm u) (τ.symm w) : ℝ≥0∞) =
          (twoBitSquareHamming (τ (τ.symm u))
            (τ (τ.symm w)) : ℝ≥0∞) :=
      congrArg (fun n : ℕ => (n : ℝ≥0∞))
        (twoBitSquareTranslation_hamming v (τ.symm u) (τ.symm w)).symm
    simpa only [Equiv.apply_symm_apply] using
      (hdist.trans ((hham (τ.symm u) (τ.symm w)).trans hHamming))

  have hcanonicalDual (u w : Fin 4) :
      fiveFibreSquareConnesDualDistance D' u.castSucc w.castSucc =
        (twoBitSquareHamming u w : ℝ≥0∞) := by
    rw [← fiveFibreLabelledConnesDistance_canonical D' u w]
    exact hcanonicalHamming u w

  have hD' : ∀ i j, D' i j = star (D' j i) :=
    fiveFibre_reindex_hermitian σ.symm D hD

  apply fiveFibreSquare_exactHamming_canonical_noGo D' hD'
  · simpa [twoBitSquareHamming] using hcanonicalDual 0 1
  · simpa [twoBitSquareHamming] using hcanonicalDual 0 2
  · simpa [twoBitSquareHamming] using hcanonicalDual 3 1
  · simpa [twoBitSquareHamming] using hcanonicalDual 3 2
  · simpa [twoBitSquareHamming] using hcanonicalDual 0 3
  · simpa [twoBitSquareHamming] using hcanonicalDual 1 2

end Neoplatonic.LTR
