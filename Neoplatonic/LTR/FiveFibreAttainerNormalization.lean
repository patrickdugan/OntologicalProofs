import Neoplatonic.LTR.FiveFibreConnesDualDistance
import Mathlib.Tactic

/-!
# LTR-MAN-31: phase-and-translation normalization of Connes dual attainers

For any admissible represented observable whose value difference across
two truth vertices has complex norm exactly two, translation by its
first value and multiplication by the complex phase 2/(f(v)-f(u))
produce another admissible observable with endpoint values 0 and 2.

The proof certifies exact invariance of the finite-dimensional Dirac
commutator under scalar translation, scalar homogeneity under complex
rescaling, and the unit modulus of the normalizing phase.

This handles normalization of attained opposite-corner witnesses in
the six-distance Hamming argument. Existence of an attainer from the
dual supremum itself is a separate compactness obligation.
-/

namespace Neoplatonic.LTR

/-- Subtracting a scalar constant from a represented observable leaves
its actual Hilbert-space Dirac commutator unchanged. -/
theorem fiveFibreSquareDiracComm_sub_const
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (f : Fin 5 → ℂ) (c : ℂ) :
    fiveFibreSquareDiracComm D (fun i => f i - c) =
      fiveFibreSquareDiracComm D f := by
  have hmatrix :
      D * Matrix.diagonal (fun i => f i - c) -
        Matrix.diagonal (fun i => f i - c) * D =
      D * Matrix.diagonal f - Matrix.diagonal f * D := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.mul_diagonal, Matrix.diagonal_mul]
    ring
  unfold fiveFibreSquareDiracComm
  rw [hmatrix]

/-- Normalize the complex phase and origin of any admissible
opposite-corner distance-two observable while retaining the
represented four-truth-vertex constraint and unit commutator norm. -/
theorem fiveFibreSquare_normalizeDistanceTwoAttainer
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (f : Fin 5 → ℂ)
    (hf : f 4 = f 0)
    (hunit : ‖fiveFibreSquareDiracComm D f‖ ≤ 1)
    (u v : Fin 5)
    (hn : ‖f v - f u‖ = 2) :
    ∃ g : Fin 5 → ℂ,
      g 4 = g 0 ∧
      ‖fiveFibreSquareDiracComm D g‖ ≤ 1 ∧
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
  let g : Fin 5 → ℂ := fun i => c * (f i - f u)
  have hgdup : g 4 = g 0 := by
    simp [g, hf]
  have hgu : g u = 0 := by
    simp [g]
  have hgv : g v = 2 := by
    change c * z = 2
    exact hcMul
  have hcomm :
      fiveFibreSquareDiracComm D g =
        c • fiveFibreSquareDiracComm D f := by
    change fiveFibreSquareDiracComm D
      (fun i => c * (f i - f u)) = _
    rw [fiveFibreSquareDiracComm_smul,
      fiveFibreSquareDiracComm_sub_const]
  have hunitG : ‖fiveFibreSquareDiracComm D g‖ ≤ 1 := by
    rw [hcomm, norm_smul, hcNorm, one_mul]
    exact hunit
  exact ⟨g, hgdup, hunitG, hgu, hgv⟩

/-- A genuine norm-two supremum attainer in the Connes admissible
subtype can be rotated and translated into the normalized witness
format required by the Hamming midpoint rigidity theorem. -/
theorem fiveFibreSquare_normalizeSubtypeAttainer
    (D : Matrix (Fin 5) (Fin 5) ℂ)
    (u v : Fin 5)
    (hatt : ∃ f : fiveFibreSquareAdmissible D,
      ‖f.val v - f.val u‖ = 2) :
    ∃ g : Fin 5 → ℂ,
      g 4 = g 0 ∧
      ‖fiveFibreSquareDiracComm D g‖ ≤ 1 ∧
      g u = 0 ∧ g v = 2 := by
  obtain ⟨f, hf⟩ := hatt
  exact fiveFibreSquare_normalizeDistanceTwoAttainer
    D f.val f.property.1 f.property.2 u v hf

end Neoplatonic.LTR
