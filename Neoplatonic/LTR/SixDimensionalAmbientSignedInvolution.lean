import Neoplatonic.LTR.SixDimensionalHilbertResidualInvolution
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Tactic

/-!
# LTR-MAN-91: lift a squared Hamming witness across the entire signed eigenquartet

The four signed extremal vectors from MAN-58 carry eigenvalues
(+1,-1,+1,-1) for either of the simultaneous Hamming witnesses
A+B and A-B (up to the sign of the B-pair).
Consequently BOTH witness squares act as identity on the entire
four-dimensional quartet span, without any saturated assumptions.

MAN-90 proves a squared identity for one true residual Hilbert
operator under MAN-89's saturation. The residual is exactly the
orthogonal complement of the quartet span, and the two submodules
are complementary in the genuine six-dimensional complex Hilbert
space.

The square-one identity therefore holds on both complementary
submodules and hence on every ambient vector. The main lemma is
general for any complete finite-dimensional complex Hilbert space.
-/

namespace Neoplatonic.LTR

private abbrev SixH := EuclideanSpace ℂ (Fin 6)

/-- If the square of a bounded Hilbert operator is identity on
a finite generating family and its orthogonal complement, it is
identity on the entire ambient complex Hilbert space. -/
theorem hilbert_square_one_of_span_and_orthogonal
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
    (T : E →L[ℂ] E) (q : Fin 4 → E)
    (hq : ∀ i : Fin 4, T (T (q i)) = q i)
    (hR : ∀ x ∈ (Submodule.span ℂ (Set.range q))ᗮ,
      T (T x) = x) :
    T * T = 1 := by
  let K := Submodule.span ℂ (Set.range q)
  have hK : ∀ x ∈ K, T (T x) = x := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨i, rfl⟩ := hx
        exact hq i
    | zero => simp
    | add x y hx hy ihx ihy =>
        simpa only [map_add] using congrArg₂ (· + ·) ihx ihy
    | smul a x hx ihx =>
        simpa only [map_smul] using
          congrArg (fun y : E => a • y) ihx
  have hsup : K ⊔ Kᗮ = ⊤ := (K.isCompl_orthogonal).sup_eq_top
  apply ContinuousLinearMap.ext
  intro x
  change T (T x) = x
  have hx : x ∈ K ⊔ Kᗮ := by
    rw [hsup]
    exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, hsum⟩ := Submodule.mem_sup.mp hx
  have hsum' : y + z = x := by
    simpa only using hsum
  rw [← hsum']
  calc
    T (T (y + z)) = T (T y) + T (T z) := by simp
    _ = y + z := by rw [hK y hy, hR z hz]

/-- The signed quartet is already pointwise an eigenfamily of
A+B with eigenvalues of square one, under the genuine paired
unit-eigenvalue and simultaneous-contraction hypotheses. -/
theorem TwoDirectionExtremalSystem.plus_square_one_on_quartet
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
    (S : TwoDirectionExtremalSystem E) (i : Fin 4) :
    (S.A + S.B) ((S.A + S.B)
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus i)) =
      twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus i := by
  let q := twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus
  let a := twoDirectionAQuartetEigenvalues
  let b := twoDirectionBQuartetEigenvalues
  have ha : S.A (q i) = a i • q i := S.eigenquartet_A i
  have hb : S.B (q i) = b i • q i := S.eigenquartet_B i
  have hT : (S.A + S.B) (q i) = (a i + b i) • q i := by
    rw [ContinuousLinearMap.add_apply, ha, hb, add_smul]
  have hsign : (a i + b i) * (a i + b i) = (1 : ℂ) := by
    fin_cases i <;>
      norm_num [a, b, twoDirectionAQuartetEigenvalues,
        twoDirectionBQuartetEigenvalues]
  calc
    (S.A + S.B) ((S.A + S.B) (q i)) =
        (S.A + S.B) ((a i + b i) • q i) := by rw [hT]
    _ = (a i + b i) • (S.A + S.B) (q i) := by rw [map_smul]
    _ = ((a i + b i) * (a i + b i)) • q i := by rw [hT, smul_smul]
    _ = q i := by rw [hsign]; simp

/-- The signed quartet is also pointwise squared-invariant
under the difference witness A-B. -/
theorem TwoDirectionExtremalSystem.minus_square_one_on_quartet
    {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [CompleteSpace E]
    (S : TwoDirectionExtremalSystem E) (i : Fin 4) :
    (S.A - S.B) ((S.A - S.B)
      (twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus i)) =
      twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus i := by
  let q := twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus
  let a := twoDirectionAQuartetEigenvalues
  let b := twoDirectionBQuartetEigenvalues
  have ha : S.A (q i) = a i • q i := S.eigenquartet_A i
  have hb : S.B (q i) = b i • q i := S.eigenquartet_B i
  have hT : (S.A - S.B) (q i) = (a i - b i) • q i := by
    rw [ContinuousLinearMap.sub_apply, ha, hb, sub_smul]
  have hsign : (a i - b i) * (a i - b i) = (1 : ℂ) := by
    fin_cases i <;>
      norm_num [a, b, twoDirectionAQuartetEigenvalues,
        twoDirectionBQuartetEigenvalues]
  calc
    (S.A - S.B) ((S.A - S.B) (q i)) =
        (S.A - S.B) ((a i - b i) • q i) := by rw [hT]
    _ = (a i - b i) • (S.A - S.B) (q i) := by rw [map_smul]
    _ = ((a i - b i) * (a i - b i)) • q i := by rw [hT, smul_smul]
    _ = q i := by rw [hsign]; simp

/-- A true square-one residual SUM makes the ambient signed
Hamming sum witness an involution on the full Hilbert space. -/
theorem TwoDirectionExtremalSystem.ambientPlus_involution_of_residual
    (S : TwoDirectionExtremalSystem SixH)
    (hr : (S.residualA + S.residualB) *
      (S.residualA + S.residualB) = 1) :
    (S.A + S.B) * (S.A + S.B) = 1 := by
  let q := twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus
  have hR : ∀ x ∈ (Submodule.span ℂ (Set.range q))ᗮ,
      (S.A + S.B) ((S.A + S.B) x) = x := by
    intro x hx
    let y : S.residual := ⟨x, hx⟩
    have hpoint : ((S.residualA + S.residualB) *
       (S.residualA + S.residualB)) y = y := by rw [hr]; rfl
    have h := congrArg (fun z : S.residual => (z : SixH)) hpoint
    change (S.A + S.B) ((S.A + S.B) x) = x at h
    exact h
  exact hilbert_square_one_of_span_and_orthogonal
    (S.A + S.B) q S.plus_square_one_on_quartet hR

/-- An involutive residual difference makes the ambient signed
Hamming difference witness a true six-dimensional involution. -/
theorem TwoDirectionExtremalSystem.ambientMinus_involution_of_residual
    (S : TwoDirectionExtremalSystem SixH)
    (hr : (S.residualA - S.residualB) *
      (S.residualA - S.residualB) = 1) :
    (S.A - S.B) * (S.A - S.B) = 1 := by
  let q := twoDirectionSignedQuartet S.uplus S.uminus S.vplus S.vminus
  have hR : ∀ x ∈ (Submodule.span ℂ (Set.range q))ᗮ,
      (S.A - S.B) ((S.A - S.B) x) = x := by
    intro x hx
    let y : S.residual := ⟨x, hx⟩
    have hpoint : ((S.residualA - S.residualB) *
       (S.residualA - S.residualB)) y = y := by rw [hr]; rfl
    have h := congrArg (fun z : S.residual => (z : SixH)) hpoint
    change (S.A - S.B) ((S.A - S.B) x) = x at h
    exact h
  exact hilbert_square_one_of_span_and_orthogonal
    (S.A - S.B) q S.minus_square_one_on_quartet hR

end Neoplatonic.LTR
