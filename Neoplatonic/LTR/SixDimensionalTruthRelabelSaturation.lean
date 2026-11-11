import Neoplatonic.LTR.SixDimensionalSaturated03Singleton11NoGo
import Neoplatonic.LTR.FiveFibreTruthTranslations
import Mathlib.Tactic

/-!
# LTR-MAN-116: truth-equivariant 6D Connes metric and signed saturation transport

The five-fibre truth-relabel equivalence from MAN-44 extends verbatim
to the actual six-dimensional Dirac commutator. A bijection of the four
truth atoms leaves the represented six-coordinate observable algebra
and Dirac seminorm unchanged after composition of the observable.

It consequently transports the exact Connes dual distances, truth-fibre
multiplicities, and all oriented squared opposite-coupling energies.

The Boolean-square translations preserve Hamming distance, so a
relabeled six-dimensional Dirac representation retains exact
Hamming distances. Translation by vertex 01 changes the surviving
opposite diagonal from 01/10 to 00/11. Applying the merged
MAN-112 positive classification proves the corresponding negative
pure-saturation classification (1,2,2,1).

All statements are about the actual labelled Hermitian Dirac matrix.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Reindexing the four truth values by any bijection carries
the actual six-coordinate admissible Dirac observables to an
equivalent unit ball without changing the Hilbert matrix. -/
noncomputable def sixLabelledTruthRelabelAdmissibleEquiv
    (τ : Fin 4 ≃ Fin 4)
    (D : SixMat)
    (label : Fin 6 → Fin 4) :
    sixLabelledAdmissible (τ ∘ label) D ≃
      sixLabelledAdmissible label D where
  toFun f := by
    refine ⟨fun i => f.val (τ i), ?_⟩
    change ‖sixLabelledDiracComm (τ ∘ label) D f.val‖ ≤ 1
    exact f.property
  invFun g := by
    refine ⟨fun i => g.val (τ.symm i), ?_⟩
    simpa [sixLabelledDiracComm, Function.comp_def] using g.property
  left_inv := by
    intro f
    apply Subtype.ext
    funext i
    simp
  right_inv := by
    intro g
    apply Subtype.ext
    funext i
    simp

/-- Any bijective truth relabeling preserves the genuine
six-dimensional Connes dual metric, after transporting endpoints. -/
theorem sixLabelledConnesDistance_truthEquiv
    (τ : Fin 4 ≃ Fin 4)
    (D : SixMat)
    (label : Fin 6 → Fin 4)
    (u v : Fin 4) :
    sixLabelledConnesDistance (τ ∘ label) D (τ u) (τ v) =
      sixLabelledConnesDistance label D u v := by
  unfold sixLabelledConnesDistance
  refine Equiv.iSup_congr
    (sixLabelledTruthRelabelAdmissibleEquiv τ D label) ?_
  intro f
  rfl

/-- A relabeled truth-atom fibre has the same multiplicity as
the original fibre at the corresponding vertex. -/
theorem sixTruthMultiplicity_truthEquiv
    (τ : Fin 4 ≃ Fin 4)
    (label : Fin 6 → Fin 4)
    (u : Fin 4) :
    truthMultiplicity (τ ∘ label) (τ u) =
      truthMultiplicity label u := by
  unfold truthMultiplicity
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Function.comp_apply]
  exact τ.injective.eq_iff

/-- The original six-dimensional Dirac matrix and its entire
oriented opposite-corner truth block are unchanged by transporting
both truth-atom endpoints along a bijection. -/
theorem sixTruthFibreBlock_truthEquiv
    (τ : Fin 4 ≃ Fin 4)
    (label : Fin 6 → Fin 4)
    (D : SixMat)
    (u v : Fin 4) :
    sixTruthFibreBlock (τ ∘ label) D (τ u) (τ v) =
      sixTruthFibreBlock label D u v := by
  ext i j
  rw [sixTruthFibreBlock_entry, sixTruthFibreBlock_entry]
  have hi : (τ (label i) = τ u) ↔ (label i = u) :=
    τ.injective.eq_iff
  have hj : (τ (label j) = τ v) ↔ (label j = v) :=
    τ.injective.eq_iff
  simp only [Function.comp_apply, hi, hj]

/-- The entire oriented squared block energy, including repeated
truth-fibre rows and columns, is invariant under truth relabeling. -/
theorem sixTruthFibreBlockEnergy_truthEquiv
    (τ : Fin 4 ≃ Fin 4)
    (label : Fin 6 → Fin 4)
    (D : SixMat)
    (u v : Fin 4) :
    sixTruthFibreBlockEnergy (τ ∘ label) D (τ u) (τ v) =
      sixTruthFibreBlockEnergy label D u v := by
  simp only [sixTruthFibreBlockEnergy,
    sixTruthFibreBlock_truthEquiv τ label D u v]

/-- The Boolean-square complement switches both truth bits:
00 ↔ 11 and 01 ↔ 10. -/
theorem twoBitSquareTranslation_three_values :
    twoBitSquareTranslation 3 0 = 3 ∧
      twoBitSquareTranslation 3 1 = 2 ∧
      twoBitSquareTranslation 3 2 = 1 ∧
      twoBitSquareTranslation 3 3 = 0 := by
  decide

/-- The genuine six-dimensional exact-Hamming Connes distances
remain exact after bitwise-complement truth relabeling. -/
theorem sixLabelled_exactHamming_bitComplement
    (label : Fin 6 → Fin 4)
    (D : SixMat)
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    let τ := twoBitSquareTranslation 3
    ∀ u v : Fin 4,
      sixLabelledConnesDistance (τ ∘ label) D u v =
        (twoBitSquareHamming u v : ℝ≥0∞) := by
  dsimp only
  let τ := twoBitSquareTranslation 3
  intro u v
  have hmetric :
      sixLabelledConnesDistance (τ ∘ label) D u v =
        sixLabelledConnesDistance label D (τ.symm u) (τ.symm v) := by
    simpa only [Equiv.apply_symm_apply] using
      (sixLabelledConnesDistance_truthEquiv
        τ D label (τ.symm u) (τ.symm v))
  rw [hmetric, hham]
  have hh : twoBitSquareHamming u v =
      twoBitSquareHamming (τ.symm u) (τ.symm v) := by
    have ht :=
      twoBitSquareTranslation_hamming 3 (τ.symm u) (τ.symm v)
    change twoBitSquareHamming (τ (τ.symm u)) (τ (τ.symm v)) =
      twoBitSquareHamming (τ.symm u) (τ.symm v) at ht
    simpa only [Equiv.apply_symm_apply] using ht
  exact congrArg (fun n : ℕ => (n : ℝ≥0∞)) hh.symm


/-- Every Boolean-square translation preserves the actual labelled
Connes metric's exact Hamming distances, including complex-valued
observables and arbitrary repeated truth fibres. -/
theorem sixLabelled_exactHamming_truthTranslation
    (label : Fin 6 → Fin 4)
    (D : SixMat)
    (w : Fin 4)
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞)) :
    let τ := twoBitSquareTranslation w
    ∀ u v : Fin 4,
      sixLabelledConnesDistance (τ ∘ label) D u v =
        (twoBitSquareHamming u v : ℝ≥0∞) := by
  dsimp only
  let τ := twoBitSquareTranslation w
  intro u v
  have hmetric :
      sixLabelledConnesDistance (τ ∘ label) D u v =
        sixLabelledConnesDistance label D (τ.symm u) (τ.symm v) := by
    simpa only [Equiv.apply_symm_apply] using
      (sixLabelledConnesDistance_truthEquiv
        τ D label (τ.symm u) (τ.symm v))
  rw [hmetric, hham]
  have hh : twoBitSquareHamming u v =
      twoBitSquareHamming (τ.symm u) (τ.symm v) := by
    have ht :=
      twoBitSquareTranslation_hamming w (τ.symm u) (τ.symm v)
    change twoBitSquareHamming (τ (τ.symm u)) (τ (τ.symm v)) =
      twoBitSquareHamming (τ.symm u) (τ.symm v) at ht
    simpa only [Equiv.apply_symm_apply] using ht
  exact congrArg (fun n : ℕ => (n : ℝ≥0∞)) hh.symm

/-- Complementing the first Boolean coordinate sends
00↔01 and 10↔11. It exchanges the two opposite diagonals. -/
theorem twoBitSquareTranslation_one_values :
    twoBitSquareTranslation 1 0 = 1 ∧
      twoBitSquareTranslation 1 1 = 0 ∧
      twoBitSquareTranslation 1 2 = 3 ∧
      twoBitSquareTranslation 1 3 = 2 := by
  decide

/-- The MAN-112 positive saturation classification transports to
the other signed Hamming witness: pure 01/10 saturation forces the
two doubled fibres at 01 and 10, and singleton fibres at 00 and 11.

The proof only changes the four truth labels. It preserves the
actual six-dimensional complex Dirac matrix. -/
theorem sixLabelled_exactHamming_saturated12_onlyOppositeDoubles
    (label : Fin 6 → Fin 4) (D : SixMat)
    (hsurj : Function.Surjective label)
    (hD : ∀ i j, D i j = star (D j i))
    (hham : ∀ u v : Fin 4,
      sixLabelledConnesDistance label D u v =
        (twoBitSquareHamming u v : ℝ≥0∞))
    (h03 : sixTruthFibreBlockEnergy label D 0 3 = 0)
    (h12 : sixTruthFibreBlockEnergy label D 1 2 = (1 / 4 : ℝ)) :
    truthMultiplicity label 0 = 1 ∧
      truthMultiplicity label 1 = 2 ∧
      truthMultiplicity label 2 = 2 ∧
      truthMultiplicity label 3 = 1 := by
  let τ := twoBitSquareTranslation 1
  obtain ⟨ht0, ht1, ht2, ht3⟩ := twoBitSquareTranslation_one_values
  have hsurj' : Function.Surjective (τ ∘ label) := by
    intro u
    obtain ⟨i, hi⟩ := hsurj (τ.symm u)
    refine ⟨i, ?_⟩
    change τ (label i) = u
    rw [hi, Equiv.apply_symm_apply]
  have hham' :
      ∀ u v : Fin 4,
        sixLabelledConnesDistance (τ ∘ label) D u v =
          (twoBitSquareHamming u v : ℝ≥0∞) :=
    sixLabelled_exactHamming_truthTranslation label D 1 hham
  have he03' :
      sixTruthFibreBlockEnergy (τ ∘ label) D 0 3 =
        (1 / 4 : ℝ) := by
    have h := sixTruthFibreBlockEnergy_truthEquiv τ label D 1 2
    rw [ht1, ht2] at h
    exact h.trans h12
  have he12' :
      sixTruthFibreBlockEnergy (τ ∘ label) D 1 2 = 0 := by
    have h := sixTruthFibreBlockEnergy_truthEquiv τ label D 0 3
    rw [ht0, ht3] at h
    exact h.trans h03
  obtain ⟨hm0', hm1', hm2', hm3'⟩ :=
    sixLabelled_exactHamming_saturated03_onlyOppositeDoubles
      (τ ∘ label) D hsurj' hD hham' he03' he12'
  have hm0 : truthMultiplicity label 0 = 1 := by
    have h := sixTruthMultiplicity_truthEquiv τ label 0
    rw [ht0] at h
    exact h.symm.trans hm1'
  have hm1 : truthMultiplicity label 1 = 2 := by
    have h := sixTruthMultiplicity_truthEquiv τ label 1
    rw [ht1] at h
    exact h.symm.trans hm0'
  have hm2 : truthMultiplicity label 2 = 2 := by
    have h := sixTruthMultiplicity_truthEquiv τ label 2
    rw [ht2] at h
    exact h.symm.trans hm3'
  have hm3 : truthMultiplicity label 3 = 1 := by
    have h := sixTruthMultiplicity_truthEquiv τ label 3
    rw [ht3] at h
    exact h.symm.trans hm2'
  exact ⟨hm0, hm1, hm2, hm3⟩

end Neoplatonic.LTR
