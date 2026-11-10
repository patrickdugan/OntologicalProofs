import Neoplatonic.LTR.SixDimensionalLabelledPauliBridge
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Tactic

/-!
# LTR-MAN-77: continuous six-dimensional labelled commutator seminorm

The actual six-dimensional Dirac commutator is linear in the four
independent complex truth values. We establish its continuity by
finite-dimensionality. Scalar translation preserves the commutator,
and a phase rotation preserves the norm of any distance-two attainer.
These are the analytic ingredients for the compact attainment step.
-/

namespace Neoplatonic.LTR

private abbrev SixH := EuclideanSpace ℂ (Fin 6)
private abbrev SixMat := Matrix (Fin 6) (Fin 6) ℂ

/-- Additivity of the genuine bounded six-dimensional commutator. -/
theorem sixLabelledDiracComm_add
    (label : Fin 6 → Fin 4) (D : SixMat)
    (f g : Fin 4 → ℂ) :
    sixLabelledDiracComm label D (f + g) =
      sixLabelledDiracComm label D f +
        sixLabelledDiracComm label D g := by
  have hmatrix :
      D * Matrix.diagonal (fun i => (f + g) (label i)) -
        Matrix.diagonal (fun i => (f + g) (label i)) * D =
      (D * Matrix.diagonal (fun i => f (label i)) -
        Matrix.diagonal (fun i => f (label i)) * D) +
      (D * Matrix.diagonal (fun i => g (label i)) -
        Matrix.diagonal (fun i => g (label i)) * D) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.add_apply,
      Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.add_apply]
    ring
  unfold sixLabelledDiracComm
  rw [hmatrix]
  ext v
  simp

/-- Scalar translation of all four truth values preserves the
actual Dirac commutator. -/
theorem sixLabelledDiracComm_sub_const
    (label : Fin 6 → Fin 4) (D : SixMat)
    (f : Fin 4 → ℂ) (c : ℂ) :
    sixLabelledDiracComm label D (fun i => f i - c) =
      sixLabelledDiracComm label D f := by
  have hmatrix :
      D * Matrix.diagonal (fun i => f (label i) - c) -
        Matrix.diagonal (fun i => f (label i) - c) * D =
      D * Matrix.diagonal (fun i => f (label i)) -
        Matrix.diagonal (fun i => f (label i)) * D := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    ring
  unfold sixLabelledDiracComm
  rw [hmatrix]

/-- The four-truth-value commutator is a complex-linear map into
genuine bounded Euclidean Hilbert operators. -/
noncomputable def sixLabelledDiracFourLinearMap
    (label : Fin 6 → Fin 4) (D : SixMat) :
    (Fin 4 → ℂ) →ₗ[ℂ] (SixH →L[ℂ] SixH) where
  toFun f := sixLabelledDiracComm label D f
  map_add' := by
    intro f g
    exact sixLabelledDiracComm_add label D f g
  map_smul' := by
    intro c f
    simpa only [Pi.smul_apply, smul_eq_mul] using
      sixLabelledDiracComm_smul label D f c

/-- The actual six-dimensional Dirac commutator norm is continuous
on the four-complex-dimensional space of truth observables. -/
theorem sixLabelledDiracFourNorm_continuous
    (label : Fin 6 → Fin 4) (D : SixMat) :
    Continuous (fun f : Fin 4 → ℂ => ‖sixLabelledDiracComm label D f‖) := by
  have hlinear : Continuous (sixLabelledDiracFourLinearMap label D) :=
    (sixLabelledDiracFourLinearMap label D).continuous_of_finiteDimensional
  exact continuous_norm.comp hlinear

/-- Rotate and translate any genuine distance-two attainer so that
its two endpoint values are exactly zero and two. -/
theorem sixLabelled_normalizeDistanceTwoAttainer
    (label : Fin 6 → Fin 4) (D : SixMat)
    (f : Fin 4 → ℂ)
    (hunit : ‖sixLabelledDiracComm label D f‖ ≤ 1)
    (u v : Fin 4)
    (hn : ‖f v - f u‖ = 2) :
    ∃ g : Fin 4 → ℂ,
      ‖sixLabelledDiracComm label D g‖ ≤ 1 ∧
      g u = 0 ∧ g v = 2 := by
  let z : ℂ := f v - f u
  have hzNorm : ‖z‖ = 2 := hn
  have hz : z ≠ 0 := by
    intro h
    have h0 : ‖z‖ = 0 := by simp [h]
    linarith
  let c : ℂ := (2 : ℂ) / z
  have hcNorm : ‖c‖ = 1 := by
    dsimp [c]
    rw [norm_div, hzNorm]
    norm_num
  have hcMul : c * z = 2 := by
    dsimp [c]
    field_simp [hz]
  let g : Fin 4 → ℂ := fun i => c * (f i - f u)
  have hgu : g u = 0 := by simp [g]
  have hgv : g v = 2 := by
    change c * z = 2
    exact hcMul
  have hcomm :
      sixLabelledDiracComm label D g =
        c • sixLabelledDiracComm label D f := by
    change sixLabelledDiracComm label D (fun i => c * (f i - f u)) = _
    rw [sixLabelledDiracComm_smul, sixLabelledDiracComm_sub_const]
  have hunitG : ‖sixLabelledDiracComm label D g‖ ≤ 1 := by
    rw [hcomm, norm_smul, hcNorm, one_mul]
    exact hunit
  exact ⟨g, hunitG, hgu, hgv⟩

/-- Normalizing a genuine admissible subtype attainer. -/
theorem sixLabelled_normalizeSubtypeAttainer
    (label : Fin 6 → Fin 4) (D : SixMat)
    (u v : Fin 4)
    (hatt : ∃ f : sixLabelledAdmissible label D,
      ‖f.val v - f.val u‖ = 2) :
    ∃ g : Fin 4 → ℂ,
      ‖sixLabelledDiracComm label D g‖ ≤ 1 ∧
      g u = 0 ∧ g v = 2 := by
  obtain ⟨f, hf⟩ := hatt
  exact sixLabelled_normalizeDistanceTwoAttainer
    label D f.val f.property u v hf

end Neoplatonic.LTR
