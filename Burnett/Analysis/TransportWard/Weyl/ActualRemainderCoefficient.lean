import Burnett.Analysis.TransportWard.Weyl.CompactRemainderDivergence
import Burnett.Analysis.TransportWard.Weyl.CompactMetricCoefficientBounds
import Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet
import Burnett.Analysis.LocalWeakDerivative

/-! The actual Gamma–Gamma remainder coefficient, extended by a fixed chart cutoff. -/

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 4500
set_option synthInstance.maxSize 4000

noncomputable section

namespace Burnett.V03

open Set Filter Burnett.Analysis.CarlesonEmbedding Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry.ConnectionDifference (coordinateBasis)
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped BigOperators ComplexConjugate ContDiff Matrix.Norms.Elementwise Topology

/-- The actual Taylor remainder with a fixed real cutoff and the original two
combined slots. It agrees with the Euler principal coefficient on a plateau. -/
def chartMetricRemainderCoefficient {ι : Type*} (S : ι → Mat) (χA : Space → ℝ)
    (G H : Space → Mat) : RemainderArray ι :=
  fun a b i j x => (χA x * principalCoefficientRemainder (metricActionCoefficient S (a, i) (b, j))
    (G x) (H x) : ℝ)

theorem chartMetricRemainderCoefficient_hermitian {ι : Type*} (S : ι → Mat) (χA : Space → ℝ)
    (G H : Space → Mat) (a b : Fin 4) (i j : ι) (x : Space) :
    conj (chartMetricRemainderCoefficient S χA G H a b i j x) =
      chartMetricRemainderCoefficient S χA G H b a j i x := by
  simp only [chartMetricRemainderCoefficient, Complex.conj_ofReal]
  rw [metricPrincipalRemainder_swap S (a,i) (b,j) (G x) (H x)]

private theorem contDiffOn_principalCoefficientRemainder_field {U : Set Space}
    {F : Mat → ℝ} (hF : ContDiffOn ℝ ∞ F nonsingularMetricDomain)
    {G H : Space → Mat} (hG : ContDiffOn ℝ ∞ G U) (hH : ContDiffOn ℝ ∞ H U)
    (h0 : MapsTo G U nonsingularMetricDomain)
    (h1 : MapsTo (fun x => G x + H x) U nonsingularMetricDomain) :
    ContDiffOn ℝ ∞ (fun x => principalCoefficientRemainder F (G x) (H x)) U := by
  unfold principalCoefficientRemainder linearTaylorRemainder
  exact (((hF.comp (hG.add hH) h1).sub (hF.comp hG h0)).sub
    (((hF.fderiv_of_isOpen isOpen_nonsingularMetricDomain (by simp)).comp hG h0).clm_apply hH)).neg

theorem chartMetricRemainderCoefficient_smooth {ι : Type*} (S : ι → Mat)
    {U : Set Space} (hU : IsOpen U) {χA : Space → ℝ} (hχA : ContDiff ℝ ∞ χA)
    (hχAU : tsupport χA ⊆ U) {G H : Space → Mat}
    (hG : ContDiffOn ℝ ∞ G U) (hH : ContDiffOn ℝ ∞ H U)
    (hseg : ∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, fieldSegment (G x) (H x) t ∈ nonsingularMetricDomain)
    (a b : Fin 4) (i j : ι) :
    ContDiff ℝ ∞ (chartMetricRemainderCoefficient S χA G H a b i j) := by
  have h0 : MapsTo G U nonsingularMetricDomain := fun x hx => by
    simpa only [fieldSegment, zero_smul, add_zero] using hseg x hx 0 (by simp)
  have h1 : MapsTo (fun x => G x + H x) U nonsingularMetricDomain := fun x hx => by
    simpa only [fieldSegment, one_smul] using hseg x hx 1 (by simp)
  exact Complex.ofRealCLM.contDiff.comp
    (Burnett.Analysis.LocalWeakDerivative.contDiff_test_mul_local hU hχA hχAU
      (contDiffOn_principalCoefficientRemainder_field
        (contDiffOn_metricActionCoefficient S (a,i) (b,j)) hG hH h0 h1))

/-- The same bound for every ordered entry after the fixed cutoff. The
background derivative and the perturbation's first derivative suffice. -/
theorem exists_chartMetricRemainderCoefficient_bounds {ι : Type*} [Fintype ι]
    (S : ι → Mat) {K : Set Mat} (hK : IsCompact K) (hKdet : K ⊆ nonsingularMetricDomain) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ {U : Set Space}, IsOpen U → ∀ {χA : Space → ℝ},
      Differentiable ℝ χA → tsupport χA ⊆ U →
      ∀ {G H : Space → Mat}, DifferentiableOn ℝ G U → DifferentiableOn ℝ H U →
      (∀ x ∈ U, ∀ t ∈ Icc (0 : ℝ) 1, fieldSegment (G x) (H x) t ∈ K) →
      ∀ (W ε P Q : ℝ), 0 ≤ W → 0 ≤ ε → 0 ≤ P → 0 ≤ Q →
      (∀ x, ‖χA x‖ ≤ W) → (∀ x, ‖fderiv ℝ χA x‖ ≤ W) →
      (∀ x ∈ U, ‖H x‖ ≤ ε) → (∀ x ∈ U, ‖fderiv ℝ G x‖ ≤ P) →
      (∀ x ∈ U, ‖fderiv ℝ H x‖ ≤ Q) →
      ∀ (a b : Fin 4) (i j : ι) (x : Space),
        ‖chartMetricRemainderCoefficient S χA G H a b i j x‖ ≤ W * M * ε^2 ∧
        ‖fderiv ℝ (chartMetricRemainderCoefficient S χA G H a b i j) x‖ ≤
          W * M * ε^2 + W * (M * ε^2 * P + M * ε * Q) := by
  let C (j : ActionSlot ι × ActionSlot ι) := metricActionCoefficient S j.1 j.2
  obtain ⟨M,hM,hCoeff⟩ := exists_field_family_derivative_bounds_on_compact C
    isOpen_nonsingularMetricDomain (fun j => contDiffOn_metricActionCoefficient S j.1 j.2) hK hKdet
  refine ⟨M,hM,?_⟩
  intro U hU χA hχA hχAU G H hG hH hseg W ε P Q hW hε hP hQ hχA₀ hχA₁ hsmall hbase hweak a b i j x
  let F := fun x => principalCoefficientRemainder (C ((a,i),(b,j))) (G x) (H x)
  let r := chartMetricRemainderCoefficient S χA G H a b i j
  by_cases hx : x ∈ U
  · have hG' := (hG x hx).differentiableAt (hU.mem_nhds hx)
    have hH' := (hH x hx).differentiableAt (hU.mem_nhds hx)
    have seg := fun t ht => hKdet (hseg x hx t ht)
    have bound := metricPrincipalRemainder_pointwise_bounds S (a,i) (b,j) G H x hG' hH' seg
      (fun t ht => (hCoeff ((a,i),(b,j)) _ (hseg x hx t ht)).2.1) hM
      (fun t ht u => by
        have bnd := (hCoeff ((a,i),(b,j)) _ (hseg x hx t ht)).2.2 (H x) (H x) u
        convert bnd using 1
        ring)
    have hF₀ : ‖F x‖ ≤ M * ε^2 := bound.1.trans (by gcongr; exact hsmall x hx)
    have hF₁ : ‖fderiv ℝ F x‖ ≤ M * ε^2 * P + M * ε * Q := bound.2.trans (by
      gcongr <;> first | exact hsmall x hx | exact hbase x hx | exact hweak x hx)
    have h0 : MapsTo G U nonsingularMetricDomain := fun y hy => by
      simpa only [fieldSegment, zero_smul, add_zero] using hKdet (hseg y hy 0 (by simp))
    have h1 : MapsTo (fun y => G y + H y) U nonsingularMetricDomain := fun y hy => by
      simpa only [fieldSegment, one_smul] using hKdet (hseg y hy 1 (by simp))
    have hFd : DifferentiableAt ℝ F x := by
      have hC := (contDiffOn_metricActionCoefficient S (a,i) (b,j))
      have hCd (z) (hz : z ∈ nonsingularMetricDomain) :=
        (hC.contDiffAt (isOpen_nonsingularMetricDomain.mem_nhds hz)).differentiableAt (by simp)
      have hDC : ContDiffOn ℝ ∞ (fderiv ℝ (metricActionCoefficient S (a,i) (b,j)))
          nonsingularMetricDomain := hC.fderiv_of_isOpen isOpen_nonsingularMetricDomain (by simp)
      have hDD := (hDC.contDiffAt
        (isOpen_nonsingularMetricDomain.mem_nhds (h0 hx))).differentiableAt (by simp)
      exact (((hCd _ (h1 hx)).comp x (hG'.add hH')).sub ((hCd _ (h0 hx)).comp x hG')).sub
        (((hDD.comp x hG').clm_apply hH')) |>.neg
    constructor
    · change ‖((χA x * F x : ℝ) : ℂ)‖ ≤ _
      rw [Complex.norm_real, norm_mul]
      calc
        _ ≤ W * (M * ε^2) := mul_le_mul (hχA₀ x) hF₀ (norm_nonneg _) hW
        _ = _ := by ring
    · have hd := (Complex.ofRealCLM.hasFDerivAt.comp x ((hχA x).hasFDerivAt.fun_mul hFd.hasFDerivAt)).fderiv
      change fderiv ℝ r x = _ at hd
      have normRealComp (D : Space →L[ℝ] ℝ) : ‖Complex.ofRealCLM.comp D‖ ≤ ‖D‖ := by
        refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun y => ?_
        change ‖((D y : ℝ) : ℂ)‖ ≤ _
        rw [Complex.norm_real]
        exact D.le_opNorm y
      change ‖fderiv ℝ r x‖ ≤ _
      rw [hd]
      refine (normRealComp _).trans ((norm_add_le _ _).trans ?_)
      rw [norm_smul, norm_smul]
      calc
        _ ≤ W * (M * ε^2 * P + M * ε * Q) + M * ε^2 * W :=
          add_le_add (mul_le_mul (hχA₀ x) hF₁ (norm_nonneg _) hW)
            (mul_le_mul hF₀ (hχA₁ x) (norm_nonneg _) (by positivity))
        _ = _ := by ring
  · have zeroNear := notMem_tsupport_iff_eventuallyEq.mp (fun hs => hx (hχAU hs))
    have hr : r =ᶠ[𝓝 x] fun _ => 0 := zeroNear.mono fun y hy => by
      change (((χA y * F y : ℝ) : ℂ)) = 0
      simp [show χA y = 0 from hy]
    change ‖r x‖ ≤ _ ∧ ‖fderiv ℝ r x‖ ≤ _
    have hzero : fderiv ℝ r x = 0 :=
      hr.fderiv_eq.trans ((hasFDerivAt_const (𝕜 := ℝ) (0 : ℂ) x).fderiv)
    simp only [hr.eq_of_nhds, hzero, norm_zero]
    exact ⟨by positivity, by positivity⟩

end Burnett.V03
