import Neoplatonic.LTR.FiveFibreLabelledConnesDistance
import Neoplatonic.LTR.FiveFibreFourTruthDual
import Mathlib.Tactic

/-!
# LTR-MAN-44: truth-label equivariance and canonical Connes dual equivalence

MAN-42 defines the Connes dual metric for any diagonal truth labeling
through its four independent complex truth values. The original
canonical metric from MAN-30 quantifies over five Hilbert-coordinate
values with the duplicated 00 truth sector constrained to agree.

Their admissible observable spaces are equivalent by the exact
faithful truth lift and restriction from MAN-32. The supremum of
pairwise differences agrees under this equivalence.

Relabeling the four truth atoms by an arbitrary equivalence transports
the dual metric's pair of arguments while preserving its value.
Combined with MAN-41's Hilbert reindexing invariance, this completes
the metric transport needed for the universal diagonal five-dimensional
no-go under MAN-40's Boolean-square translations.
-/

namespace Neoplatonic.LTR

open scoped NNReal ENNReal

/-- The canonical represented observable is the literal lift of its
four complex truth values, including the duplicated 00 fibre. -/
theorem fiveFibreLift_eq_canonical_comp (f : Fin 4 → ℂ) :
    fiveFibreSquareLift f = f ∘ fiveFibreCanonicalLabel := by
  funext i
  fin_cases i <;>
    simp [fiveFibreSquareLift, fiveFibreCanonicalLabel]

/-- Equivalence of the two actual admissible-observable subtypes:
four truth values versus five represented coordinates constrained
by the repeated value at the fifth Hilbert position. -/
noncomputable def fiveFibreCanonicalAdmissibleEquiv
    (D : Matrix (Fin 5) (Fin 5) ℂ) :
    fiveFibreLabelledAdmissible fiveFibreCanonicalLabel D ≃
      fiveFibreSquareAdmissible D where
  toFun f := by
    have hdup :
        fiveFibreSquareLift f.val 4 =
          fiveFibreSquareLift f.val 0 := by
      simp [fiveFibreSquareLift]
    have hunit :
        ‖fiveFibreSquareDiracComm D (fiveFibreSquareLift f.val)‖ ≤ 1 := by
      rw [fiveFibreLift_eq_canonical_comp]
      exact f.property
    exact ⟨fiveFibreSquareLift f.val, ⟨hdup, hunit⟩⟩
  invFun g := by
    have hunit :
        ‖fiveFibreLabelledDiracComm
          fiveFibreCanonicalLabel D
          (fiveFibreSquareRestrict g.val)‖ ≤ 1 := by
      change ‖fiveFibreSquareDiracComm D
          ((fiveFibreSquareRestrict g.val) ∘ fiveFibreCanonicalLabel)‖ ≤ 1
      rw [← fiveFibreLift_eq_canonical_comp,
        fiveFibreSquareLift_restrict g.val g.property.1]
      exact g.property.2
    exact ⟨fiveFibreSquareRestrict g.val, hunit⟩
  left_inv := by
    intro f
    apply Subtype.ext
    funext i
    simp [fiveFibreSquareRestrict, fiveFibreSquareLift]
  right_inv := by
    intro g
    apply Subtype.ext
    exact fiveFibreSquareLift_restrict g.val g.property.1

/-- The labelled canonical Connes dual distance is exactly the
original five-coordinate extended Connes dual metric. -/
theorem fiveFibreLabelledConnesDistance_canonical
    (D : Matrix (Fin 5) (Fin 5) ℂ) (u v : Fin 4) :
    fiveFibreLabelledConnesDistance
      fiveFibreCanonicalLabel D u v =
    fiveFibreSquareConnesDualDistance
      D u.castSucc v.castSucc := by
  unfold fiveFibreLabelledConnesDistance
    fiveFibreSquareConnesDualDistance
  refine Equiv.iSup_congr (fiveFibreCanonicalAdmissibleEquiv D) ?_
  intro f
  simp [fiveFibreCanonicalAdmissibleEquiv,
    fiveFibreSquareLift_castSucc]

/-- A truth-atom bijection induces an actual equivalence of the
admissible truth-observable spaces, by precomposition. -/
noncomputable def fiveFibreTruthRelabelAdmissibleEquiv
    (τ : Fin 4 ≃ Fin 4)
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (label : Fin 5 → Fin 4) :
    fiveFibreLabelledAdmissible (τ ∘ label) D ≃
      fiveFibreLabelledAdmissible label D where
  toFun f := by
    refine ⟨fun i => f.val (τ i), ?_⟩
    change ‖fiveFibreSquareDiracComm D
      (fun k => f.val (τ (label k)))‖ ≤ 1
    exact f.property
  invFun g := by
    refine ⟨fun i => g.val (τ.symm i), ?_⟩
    change ‖fiveFibreSquareDiracComm D
      (fun k => g.val (τ.symm (τ (label k))))‖ ≤ 1
    simpa using g.property
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

/-- Any bijection of the four truth atoms preserves the actual
Connes dual distance after relabeling the represented observable
and both distance arguments. -/
theorem fiveFibreLabelledConnesDistance_truthEquiv
    (τ : Fin 4 ≃ Fin 4)
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (label : Fin 5 → Fin 4)
    (u v : Fin 4) :
    fiveFibreLabelledConnesDistance
      (τ ∘ label) D (τ u) (τ v) =
    fiveFibreLabelledConnesDistance label D u v := by
  unfold fiveFibreLabelledConnesDistance
  refine Equiv.iSup_congr
    (fiveFibreTruthRelabelAdmissibleEquiv τ D label) ?_
  intro f
  rfl

/-- Conjugate-symmetry of a Dirac matrix persists under a simultaneous
Hilbert coordinate permutation. -/
theorem fiveFibre_reindex_hermitian
    (e : Fin 5 ≃ Fin 5)
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (hD : ∀ i j, D i j = star (D j i)) :
    ∀ i j, (Matrix.reindex e e D) i j =
      star ((Matrix.reindex e e D) j i) := by
  intro i j
  change D (e.symm i) (e.symm j) =
    star (D (e.symm j) (e.symm i))
  exact hD _ _

end Neoplatonic.LTR
