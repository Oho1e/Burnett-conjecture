import Burnett.Analysis.TransportPatches.IntrinsicProjectedSupport
import Burnett.Analysis.TransportPatches.WholeCosphereDefectNorm
import Burnett.Analysis.GaugeProjection.ProjectedDefectActualComponents

/-! Strong whole-space L² disappearance of the actual complementary gradient. -/

set_option autoImplicit false
set_option maxRecDepth 5200
set_option maxHeartbeats 6800000

noncomputable section

namespace Burnett.C02

open Set Filter Function MeasureTheory Matrix Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.RicciSymbol (Index Tensor2)
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Microlocal.SeparablePositive (productSymbol productSymbol_apply fourierMultiplier_product)
open Burnett.P01 (regularizedProjectionComponentSymbol principalProjectionComponentSymbol_apply
  regularizedGaugeProjectionSymbol regularizedGaugeProjectionSymbol_zero
  regularizedGaugeProjectionSymbol_contDiff gaugeProjectionSymbol_contDiffOn
  gaugeProjectionSymbol_scale principalGaugeProjectionMatrix receivingCutoffFluctuation)
open Burnett.A02.FrequencySplit (tau mikhlin_bounded_symbol)
open Burnett.Analysis.ProjectiveNullCaps (thinConeProfile thinConeProfile_contDiffOn thinConeProfile_degreeZero)
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ContDiff Manifold Matrix Topology

open private regularizedProjectionComponentSymbol_eq_off_ball
  from Burnett.Analysis.GaugeProjection.ProjectedDefectActualComponents

local notation "E" => CoordinateSpace

private theorem thinComplement_contDiffOn (m : Tensor2) {η : ℝ} (hη : 0 < η) (i o : ℝ) :
    ContDiffOn ℝ ∞ (fun ξ : E => 1 - thinConeProfile m η i o ξ) ({0}ᶜ : Set E) :=
  contDiffOn_const.sub (thinConeProfile_contDiffOn m hη i o)

private theorem exists_thinComplementScalar (m : Tensor2) {η : ℝ} (hη : 0 < η) (i o : ℝ) :
    ∃ a : BoundedSymbol E, ∀ ξ, a ξ = ((1 - thinConeProfile m η i o ξ : ℝ) : ℂ) :=
  mikhlin_bounded_symbol _ (thinComplement_contDiffOn m hη i o)
    (fun t ht ξ => by rw [thinConeProfile_degreeZero m η i o t ht.ne' ξ])

def thinComplementScalar (m : Tensor2) {η : ℝ} (hη : 0 < η) (i o : ℝ) : BoundedSymbol E :=
  Classical.choose (exists_thinComplementScalar m hη i o)

theorem thinComplementScalar_apply (m : Tensor2) {η : ℝ} (hη : 0 < η) (i o : ℝ) (ξ : E) :
    thinComplementScalar m hη i o ξ = ((1 - thinConeProfile m η i o ξ : ℝ) : ℂ) :=
  Classical.choose_spec (exists_thinComplementScalar m hη i o) ξ

/-- Apply the genuine thin complement to the original fixed infrared-regularized
Euclidean projector. The full entries are smooth even at zero. -/
def actualThinConeComplementMultiplier (m : Tensor2) {η : ℝ} (hη : 0 < η) (inner outer : ℝ) :
    ClassicalMatrixMultiplier OrderedPair where
  full k i := productSymbol (thinComplementScalar m hη inner outer)
    (regularizedProjectionComponentSymbol k.1 k.2 i.1 i.2)
  principal := thinConeComplementMatrix m η inner outer
  full_smooth k i := by
    let f (ξ : E) := productSymbol (thinComplementScalar m hη inner outer)
      (regularizedProjectionComponentSymbol k.1 k.2 i.1 i.2) ξ
    change ContDiff ℝ ∞ f
    have hF (ξ : E) : f ξ = ((1 - thinConeProfile m η inner outer ξ : ℝ) : ℂ) *
        (regularizedGaugeProjectionSymbol k.1 k.2 i.1 i.2 (tau • ξ) : ℂ) := by
      dsimp only [f]
      rw [productSymbol_apply, thinComplementScalar_apply]
      rfl
    have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
    rw [contDiff_iff_contDiffAt]
    intro ξ
    by_cases hξ : ξ = 0
    · subst ξ
      have hNear : ∀ᶠ ξ in 𝓝 (0 : E), ‖ξ‖ < 1 / tau :=
        (continuous_norm.tendsto (0 : E)).eventually (Iio_mem_nhds (by simpa using one_div_pos.mpr hτ))
      have hZero : f =ᶠ[𝓝 (0 : E)] (fun _ : E => (0 : ℂ)) := by
        filter_upwards [hNear] with ξ hξ
        have hg : ‖tau • ξ‖ ≤ 1 := by
          rw [norm_smul, Real.norm_of_nonneg hτ.le, mul_comm]
          exact ((lt_div_iff₀ hτ).1 hξ).le
        rw [hF, regularizedGaugeProjectionSymbol_zero _ _ _ _ hg, Complex.ofReal_zero, mul_zero]
      exact contDiffAt_const.congr_of_eventuallyEq hZero
    · have hm := (Complex.ofRealCLM.contDiff.comp_contDiffOn
        (thinComplement_contDiffOn m hη inner outer)).contDiffAt
        (isOpen_compl_singleton.mem_nhds hξ)
      have hg : ContDiff ℝ ∞ (fun ξ : E =>
          (regularizedGaugeProjectionSymbol k.1 k.2 i.1 i.2 (tau • ξ) : ℂ)) :=
        Complex.ofRealCLM.contDiff.comp ((regularizedGaugeProjectionSymbol_contDiff _ _ _ _).comp
          (contDiff_const.smul contDiff_id))
      exact ((hm.mul hg.contDiffAt).congr_of_eventuallyEq (Eventually.of_forall hF))
  principal_smooth k i := by
    change ContDiffOn ℝ ∞ (fun ξ : E => ((1 - thinConeProfile m η inner outer ξ : ℝ) : ℂ) *
      (P01.gaugeProjectionSymbol k.1 k.2 i.1 i.2 ξ : ℂ)) ({0}ᶜ : Set E)
    exact (Complex.ofRealCLM.contDiff.comp_contDiffOn (thinComplement_contDiffOn m hη inner outer)).mul
      (Complex.ofRealCLM.contDiff.comp_contDiffOn (gaugeProjectionSymbol_contDiffOn _ _ _ _))
  principal_degree k i t ht ξ _ := by
    change ((1 - thinConeProfile m η inner outer (t • ξ) : ℝ) : ℂ) *
      (P01.gaugeProjectionSymbol k.1 k.2 i.1 i.2 (t • ξ) : ℂ) =
      ((1 - thinConeProfile m η inner outer ξ : ℝ) : ℂ) *
        (P01.gaugeProjectionSymbol k.1 k.2 i.1 i.2 ξ : ℂ)
    rw [thinConeProfile_degreeZero m η inner outer t ht.ne' ξ, gaugeProjectionSymbol_scale _ _ _ _ t ht]
  order_minus_one k i := by
    refine ⟨2 / tau + 1, 0, le_rfl, ?_⟩
    intro ξ hξ
    have hOut : ξ ∉ Metric.closedBall 0 (2 / tau) := by
      rw [Metric.mem_closedBall, dist_zero_right, not_le]
      exact (lt_add_of_pos_right _ zero_lt_one).trans_le hξ
    have hEq := regularizedProjectionComponentSymbol_eq_off_ball k.1 k.2 i.1 i.2 ξ hOut
    rw [productSymbol_apply, thinComplementScalar_apply, hEq, principalProjectionComponentSymbol_apply]
    change (1 + ‖ξ‖) * ‖(((1 - thinConeProfile m η inner outer ξ : ℝ) : ℂ) *
      (P01.gaugeProjectionSymbol k.1 k.2 i.1 i.2 ξ : ℂ)) -
      (((1 - thinConeProfile m η inner outer ξ : ℝ) : ℂ) *
      (P01.gaugeProjectionSymbol k.1 k.2 i.1 i.2 ξ : ℂ))‖ ≤ 0
    simp

theorem actualThinConeComplementMultiplier_output (m : Tensor2) {η : ℝ} (hη : 0 < η) (inner outer : ℝ)
    (u : OrderedPair → ComplexL2 E) (k : OrderedPair) :
    (actualThinConeComplementMultiplier m hη inner outer).output u k =
      fourierMultiplier (thinComplementScalar m hη inner outer)
        (∑ i : OrderedPair, fourierMultiplier (regularizedProjectionComponentSymbol k.1 k.2 i.1 i.2) (u i)) := by
  simp only [ClassicalMatrixMultiplier.output, actualThinConeComplementMultiplier, map_sum, fourierMultiplier_product]

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The thin complement of the actual regularized physical field has gradient
strongly zero in whole-space L² along the unchanged quadratic subsequence. -/
theorem exists_actualThinConeComplement_tendsto_zero
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hn σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hn σ A)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x₀ ∈ K, ∀ ℓ : ℝ, (∀ x ∈ K, ‖x - x₀‖ ≤ ℓ) →
      ∀ (η inner outer : ℝ) (hη : 0 < η), 0 ≤ inner → inner < outer → L * ℓ ≤ inner * η →
      ∀ (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ K),
      let z := receivingCutoffFluctuation B g hB hg c χ (hχ.trans hKU)
      let T := actualThinConeComplementMultiplier (chartInverseMetric B c x₀) hη inner outer
      Tendsto (fun n => WithLp.toLp 2 (fun a : Index × OrderedPair =>
        multiplierCoordinateDerivative T (z (σ n)) a.1 a.2)) atTop (𝓝 0) := by
  obtain ⟨L, hL, hAnn⟩ := exists_thinConeComplement_annihilates_originalAmplitude r B g hB hg hs hn σ A
    hA c K hK hConv hKU
  refine ⟨L, hL, ?_⟩
  intro x₀ hx₀ ℓ hℓ η inner outer hη hInner hIO hSmall χ hχ z T
  let K₀ := c.chart.symm '' K
  have hK₀ : IsCompact K₀ := hK.image_of_continuousOn (c.chart.continuousOn_symm.mono hKU)
  have hK₀c : K₀ ⊆ c.chart.source := image_subset_iff.mpr (c.chart.symm.mapsTo.mono_left hKU)
  have hχ₀ : tsupport (χ : E → ℝ) ⊆ c.chart '' K₀ := by
    intro x hx
    exact ⟨c.chart.symm x, ⟨x, hχ hx, rfl⟩, c.chart.right_inv (hKU (hχ hx))⟩
  let τ := A.control.restrict (amplitudeCosphereWindow r K₀)
  let H := globalDefectNormIntegrand B c χ T A
  have hLim : Tendsto (fun n => ∑ d : Index, ∑ k : OrderedPair,
      ‖multiplierCoordinateDerivative T (z (σ n)) d k‖^2) atTop (𝓝 (∫ p, H p ∂τ)) :=
    (tendsto_originalGlobalDefectNorm r B g hB hg hn hconv σ hσ A hPair c K₀ hK₀ hK₀c χ hχ₀ T).2
  have hZero : H =ᵐ[τ] 0 := by
    filter_upwards [hAnn x₀ hx₀ ℓ hℓ η inner outer hη hInner hIO hSmall] with p hp
    let ξ : E := WithLp.toLp 2 (atlasChartUnitCovector c p)
    have hp' : T.principal ξ * atlasAmplitudeMatrix c A.density p = 0 := hp
    have hProd : T.principal ξ * chartLebesgueAmplitude B c A p = 0 := by
      simp only [chartLebesgueAmplitude, Matrix.mul_smul, hp', smul_zero]
    change ((χ : E → ℝ) (Geometry.FixedCotangentChart.fixedChartPhase c p.val).1)^2 *
      ‖ξ‖^2 * (T.principal ξ * chartLebesgueAmplitude B c A p * (T.principal ξ)ᴴ).trace.re = 0
    simp [hProd]
  have hIeq := integral_congr_ae hZero
  simp only [Pi.zero_apply, integral_zero] at hIeq
  rw [hIeq] at hLim
  have hE : Tendsto (fun n => ‖WithLp.toLp 2 (fun a : Index × OrderedPair =>
      multiplierCoordinateDerivative T (z (σ n)) a.1 a.2)‖^2) atTop (𝓝 0) := by
    simpa only [multiplierCoordinateDerivative_norm_sq] using hLim
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hRoot := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hE
  change Tendsto (fun n => Real.sqrt (‖WithLp.toLp 2 (fun a : Index × OrderedPair =>
    multiplierCoordinateDerivative T (z (σ n)) a.1 a.2)‖^2)) atTop (𝓝 (Real.sqrt 0)) at hRoot
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hRoot

end Burnett.C02
