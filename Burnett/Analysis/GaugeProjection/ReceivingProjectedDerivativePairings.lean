import Burnett.Analysis.GaugeProjection.ProjectedDefectMixedMetricPairings
import Burnett.Analysis.GaugeProjection.MaximalChartUniformSource
import Burnett.Analysis.GaugeProjection.StrongCompactness.HomogeneousReceivingBridge
import Burnett.Analysis.Microlocal.Overlap.ReceivingSeparablePairing
import Burnett.Analysis.Microlocal.Overlap.IntrinsicJetAmplitudeMeasure

set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 9000000

noncomputable section

namespace Burnett.P01

open Set Filter Function MeasureTheory Matrix Burnett.Geometry Burnett.Fourier Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Microlocal.Overlap Burnett.Microlocal.AtlasVolumeGradient
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Geometry.UnitNullCompactness (CotangentBundle)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase measurable_fixedChartPhase_comp)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.AngularCommutator (DegreeZero measurable_of_angular_smooth)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.SeparablePositive (separableOperator)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open Burnett.A07 (coordinateDerivative)
open scoped ComplexConjugate ContDiff InnerProduct Manifold Matrix Topology

open private gaugePairTest gaugePairTest_smooth projectedCovariance_integrand
  from Burnett.Analysis.GaugeProjection.ProjectedDefectMatrixPairing

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The full separated angular tests of the projected localized derivatives
on the original intrinsic control and along the original subsequence. -/
def HasReceivingProjectedDerivativePairings
    (r : Metric (M := M)) (B : Field (M := M)) (c : AtlasChart M)
    (K : Set M) (χ : D) (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r)
    (z : ℕ → ProjectionSchwartzMatrix) : Prop :=
  ∃ d : D, EqOn (d : E → ℝ) (fixedHalfDensity B c) (tsupport (χ : E → ℝ)) ∧
    ∀ (α β : Index) (m : BoundedSymbol E) (a : D),
      ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E) → DegreeZero (m : E → ℂ) →
      ∀ i j : OrderedPair,
        let V (s : Index) (n : ℕ) (k : OrderedPair) := symbolCLM (physicalCoefficient d)
          ((coordinateDerivative s (projectionFullSchwartz (z (σ n)) k.1 k.2)).toLp 2 volume)
        let τ := A.control.restrict (amplitudeCosphereWindow r K)
        let F (p : Cosphere r) :=
          let x := (fixedChartPhase c p.val).1
          let ξ := WithLp.toLp 2 (atlasChartUnitCovector c p)
          let P := principalGaugeProjectionMatrix ξ
          physicalCoefficient a x * m ξ *
            ((((χ : E → ℝ) x : ℝ) : ℂ)^2 * ((ξ α : ℂ) * (ξ β : ℂ))) *
            (P * atlasAmplitudeMatrix c A.density p * Pᴴ) j i
        Integrable F τ ∧ Tendsto (fun n => inner ℂ (V α n i)
          (symbolCLM (physicalCoefficient a) (fourierMultiplier m (V β n j))))
          atTop (𝓝 (∫ p, F p ∂τ))

private theorem receiving_orderedJet_integrable
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source) (i j : JetSlot) :
    Integrable (fun p => atlasOrderedJetEntry c A.density p i j)
      (A.control.restrict (amplitudeCosphereWindow r K)) := by
  have hI := (original_intrinsicJetAmplitude_positive_and_integrable r B g hB hg hsB hsG
    hnB hnG hconv hb hv σ hσ A hA).2 c hK hKc j i
  refine hI.congr ?_
  have hWin := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  filter_upwards [ae_restrict_mem (μ := A.control) hWin] with p hp
  exact atlasIntrinsicJetComponent_eq_ordered c A.density p (hKc hp) j i

/-- Projection acts on both angular covariance slots of the actual zero
extension in any maximal chart, with one fixed background half-density. -/
theorem hasReceivingProjectedDerivativePairings_of_originalIntrinsicAmplitude
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart '' K) :
    let hχc := hχ.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    HasReceivingProjectedDerivativePairings r B c K χ σ A (receivingCutoffFluctuation B g hB hg c χ hχc) := by
  intro hχc
  let L := tsupport (χ : E → ℝ)
  have hL : IsCompact L := test_compactSupport χ
  let Gc (H : Field (M := M)) := metricComponents (fixedForm H c)
  obtain ⟨G, G₀, hG, hG₀, nearG, nearG₀⟩ := exists_openChartMetricRepresentatives
    hL c.chart.open_target hχc (fun n => Gc (g n)) (Gc B)
    (fun n => fixedForm_components_smooth (g n) (hg n) c) (fixedForm_components_smooth B hB c)
  have agree n x (hx : x ∈ L) := (nearG n).filter_mono (nhds_le_nhdsSet hx)
  have agree₀ x (hx : x ∈ L) := nearG₀.filter_mono (nhds_le_nhdsSet hx)
  have hConvG : TendstoUniformlyOn G G₀ atTop L :=
    ((fixed_components_uniform_of_physical_C0loc r g B hconv c L hL hχc).congr
      (Eventually.of_forall fun n x hx => (agree n x hx).eq_of_nhds.symm)).congr_right
      (fun x hx => (agree₀ x hx).eq_of_nhds.symm)
  obtain ⟨C, hC, hJet⟩ := fixedJet_uniform_bound_on_compact r g B hg hB hnB hconv hb c hL hχc
  have hDeriv (n : ℕ) (i j : Index) (x : E) (hx : x ∈ L) :
      ‖fderiv ℝ (fun y => G n y i j - G₀ y i j) x‖ ≤ 4 * C := by
    have he : (fun y => G n y i j - G₀ y i j) =ᶠ[𝓝 x]
        (fun y => Gc (g n) y i j - Gc B y i j) :=
      by
        filter_upwards [agree n x hx, agree₀ x hx] with y hn h₀
        simp only [hn, h₀]
    rw [he.fderiv_eq]
    apply coordinate_opNorm_le _ C hC
    intro b
    let J := coordinateJet (fun y => Gc (g n) y - Gc B y) x
    change ‖J b i j‖ ≤ C
    exact (norm_le_pi_norm (J b i) j).trans ((norm_le_pi_norm (J b) i).trans
      ((norm_le_pi_norm J b).trans (hJet n x hx)))
  obtain ⟨θ, hθ, hθc, hθU, V, _, hLV, _, hθV⟩ := exists_projectedChartCutoff hL c.chart.open_target hχc
  let e : D := ⟨θ, hθ, hθc⟩
  let d := fixedWeightedCutoff B hB hnB c e hθU
  have hd : EqOn (d : E → ℝ) (fixedHalfDensity B c) L := by
    intro x hx
    change θ x * fixedHalfDensity B c x = _
    rw [show θ x = 1 from hθV (hLV hx), one_mul]
  let z n := localizedMetricSchwartz (G n) G₀ χ (test_smooth χ) hL (hG n) hG₀
  have hz : z = receivingCutoffFluctuation B g hB hg c χ hχc := by
    funext n i j
    ext x
    change (((χ : E → ℝ) x * (G n x i j - G₀ x i j) : ℝ) : ℂ) =
      (((χ : E → ℝ) x * fixedPerturbation B (g n) c x i j : ℝ) : ℂ)
    by_cases hx : x ∈ L
    · rw [(agree n x hx).eq_of_nhds, (agree₀ x hx).eq_of_nhds]
      rfl
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  let W (s : Index) (n : ℕ) (k : OrderedPair) :=
    (fixedVolumeGradientSchwartz B g hB hg hnB c χ hχc (σ n) (s, k)).toLp 2 volume
  have hW (s : Index) (n : ℕ) (k : OrderedPair) : (W s n k : E → ℂ) =ᵐ[volume] fun y =>
      (((d : E → ℝ) y * (χ : E → ℝ) y *
        (coordinateJet (G (σ n)) y s k.1 k.2 - coordinateJet G₀ y s k.1 k.2) : ℝ) : ℂ) := by
    filter_upwards [(fixedVolumeGradientSchwartz B g hB hg hnB c χ hχc (σ n) (s, k)).coeFn_toLp 2 volume]
      with y hy
    rw [show W s n k y = _ from hy, fixedVolumeGradientSchwartz_apply]
    by_cases hyL : y ∈ L
    · have hNear : (fun x => G (σ n) x - G₀ x) =ᶠ[𝓝 y]
          fixedPerturbation B (g (σ n)) c := by
        filter_upwards [agree (σ n) y hyL, agree₀ y hyL] with x hn h₀
        rw [hn, h₀]
        rfl
      have hJ := projectedChart_coordinateJet_eq_of_eventuallyEq hNear
      have he := congrFun (congrFun (congrFun hJ s) k.1) k.2
      have hSub : coordinateJet (fun x => G (σ n) x - G₀ x) y s k.1 k.2 =
          coordinateJet (G (σ n)) y s k.1 k.2 - coordinateJet G₀ y s k.1 k.2 := by
        simp only [coordinateJet, Pi.sub_apply, fderiv_fun_sub
          ((hG (σ n) k.1 k.2).differentiable (by simp) y)
          ((hG₀ k.1 k.2).differentiable (by simp) y), ContinuousLinearMap.sub_apply]
      rw [← he, hSub, hd hyL]
      push_cast
      ring
    · simp [image_eq_zero_of_notMem_tsupport hyL]
  obtain ⟨C₀, _, hBound, _⟩ := fixedVolumeGradient_weak_and_uniform_L2 r B g hB hg hnB hconv hb c χ hχc
  rw [← hz]
  refine ⟨d, hd, ?_⟩
  intro α β m a hm hm₀ i j U τ F
  let x (p : Cosphere r) := (fixedChartPhase c p.val).1
  let ξ (p : Cosphere r) := WithLp.toLp 2 (atlasChartUnitCovector c p)
  let w (p : Cosphere r) := ((χ : E → ℝ) (x p) : ℂ)^2
  let N (p : Cosphere r) := w p • atlasAmplitudeMatrix c A.density p
  let b := physicalCoefficient a
  have hbS : ContDiff ℝ ∞ (b : E → ℂ) := Complex.ofRealCLM.contDiff.comp (test_smooth a)
  have hbC : HasCompactSupport (b : E → ℂ) := by
    apply (test_compactSupport a).of_isClosed_subset isClosed_closure
    apply closure_mono
    intro y hy hzero
    exact hy (by simp [b, physicalCoefficient, hzero])
  have hPhase := measurable_fixedChartPhase_comp (Subtype.val : Cosphere r → CotangentBundle M)
    continuous_subtype_val c
  have hx : Measurable x := hPhase.fst
  have hξ : Measurable ξ := ((PiLp.continuous_toLp 2 (fun _ : Index => ℝ)).measurable.comp hPhase.snd)
  let τ₀ := A.control.restrict (amplitudeCosphereWindow r K)
  have hN (k l : OrderedPair) :
      Integrable (fun p => ((ξ p α : ℂ) * (ξ p β : ℂ)) * N p k l) τ₀ := by
    have hI := receiving_orderedJet_integrable r B g hB hg hsB hsG hnB hnG hconv hb hv σ hσ A hA c K
      hK hKc (α, l) (β, k)
    have hχM := Complex.continuous_ofReal.measurable.comp ((test_smooth χ).continuous.measurable.comp hx)
    have hwM : Measurable w := by simpa only [w, pow_two, Function.comp_apply] using hχM.mul hχM
    have hwI := hI.bdd_mul hwM.aestronglyMeasurable
      ⟨(physicalCoefficient χ).bound ^ 2, fun p => by
        change ‖((physicalCoefficient χ) (x p))^2‖ ≤ (physicalCoefficient χ).bound ^ 2
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) ((physicalCoefficient χ).norm_le _) 2⟩
    convert hwI using 1
    funext p
    simp only [N, Matrix.smul_apply, smul_eq_mul, atlasOrderedJetEntry, ξ, PiLp.toLp_apply]
    ring
  have hPair (k l : OrderedPair) (m₁ : BoundedSymbol E)
      (hm₁ : ContDiffOn ℝ ∞ (m₁ : E → ℂ) ({0}ᶜ : Set E)) (hm₁₀ : DegreeZero (m₁ : E → ℂ)) :
      Tendsto (fun n => inner ℂ (W α n k) (symbolCLM b (fourierMultiplier m₁ (W β n l)))) atTop
        (𝓝 (∫ p, b (x p) * m₁ (ξ p) * ((ξ p α : ℂ) * (ξ p β : ℂ)) * N p l k ∂τ₀)) := by
    obtain ⟨_, hPair₀⟩ := tendsto_originalVolume_receivingSeparablePairing
      r B g hB hg hsB hsG hnB hnG hconv hb hv σ hσ A hA c K hK hKc b m₁ hbS hbC hm₁ hm₁₀
      χ χ hχ hχ (α, k) (β, l)
    have hWin := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
    have he : ∀ᵐ p ∂τ₀, receivingClassicalTest c A (fun y q => b y * m₁ q) χ χ (α, k) (β, l) p =
        b (x p) * m₁ (ξ p) * ((ξ p α : ℂ) * (ξ p β : ℂ)) * N p l k := by
      filter_upwards [ae_restrict_mem (μ := A.control) hWin] with p hp
      have hmEq := atlasAngularPhaseCode_symbol_eq_unitCovector c p (hKc hp) (fun _ => (m₁ : E → ℂ))
        (fun _ => hm₁₀)
      change m₁ (atlasAngularPhaseCode c p).2.val = m₁ (ξ p) at hmEq
      simp only [receivingClassicalTest, show (atlasAngularPhaseCode c p).1 = x p from rfl, hmEq,
        atlasOrderedJetEntry, ξ, PiLp.toLp_apply, N, Matrix.smul_apply, smul_eq_mul, w, pow_two, physicalCoefficient]
      ring
    change Tendsto (fun n => inner ℂ (W α n k) (symbolCLM b (fourierMultiplier m₁ (W β n l)))) atTop
      (𝓝 (∫ p, receivingClassicalTest c A (fun y q => b y * m₁ q) χ χ (α, k) (β, l) p ∂τ₀)) at hPair₀
    rw [integral_congr_ae he] at hPair₀
    exact hPair₀
  have ht := projectedLocalizedMetric_weighted_mixedPairing_tendsto τ₀ x ξ N hx hξ m b hm hm₀
    (fun y => Complex.conj_ofReal (a.val y)) hbS.continuous.measurable hbS hbC
    c.chart.target c.chart.open_target (G ∘ σ) G₀ χ (test_smooth χ) hL hχc (fun n => hG (σ n)) hG₀
    (fun s hs => hσ.tendsto_atTop.eventually (hConvG s hs)) ⟨4 * C, by positivity⟩ (fun n => hDeriv (σ n))
    d (physicalCoefficient d) (fun _ => rfl) W hW C₀ (fun s n k => hBound (σ n) (s, k))
    α β hN hPair i j
  let N' (p : Cosphere r) := ((ξ p α : ℂ) * (ξ p β : ℂ)) • N p
  have hF :
      F = fun p => b (x p) * m (ξ p) *
        (principalGaugeProjectionMatrix (ξ p) * N' p * (principalGaugeProjectionMatrix (ξ p))ᴴ) j i := by
    funext p
    simp only [F, N', N, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, w, ξ, x, b]
    ring
  refine ⟨?_, ?_⟩
  · rw [hF]
    have hEach (k l : OrderedPair) : Integrable
        (fun p => b (x p) * gaugePairTest m i j k l (ξ p) * N' p l k) τ₀ := by
      have hI : Integrable (fun p => N' p l k) τ₀ := hN l k
      apply hI.bdd_mul
      · exact ((hbS.continuous.measurable.comp hx).mul
          ((measurable_of_angular_smooth _ (gaugePairTest_smooth m hm i j k l)).comp hξ)).aestronglyMeasurable
      · exact ⟨b.bound * (gaugePairTest m i j k l).bound, fun p => by
          rw [norm_mul]
          exact mul_le_mul (b.norm_le _) ((gaugePairTest m i j k l).norm_le _) (norm_nonneg _) b.bound_nonneg⟩
    exact (integrable_finset_sum _ (fun k _ => integrable_finset_sum _ (fun l _ => hEach k l))).congr
      (Eventually.of_forall fun p => projectedCovariance_integrand m b i j (x p) (ξ p) (N' p))
  · rw [hF]
    have hEq (p : Cosphere r) :
        b (x p) * m (ξ p) * ((ξ p α : ℂ) * (ξ p β : ℂ)) *
          (principalGaugeProjectionMatrix (ξ p) * N p * (principalGaugeProjectionMatrix (ξ p))ᴴ) j i =
        b (x p) * m (ξ p) *
          (principalGaugeProjectionMatrix (ξ p) * N' p * (principalGaugeProjectionMatrix (ξ p))ᴴ) j i := by
      simp only [N', Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
      ring
    simpa only [hEq, U, z, Function.comp_apply] using ht

end Burnett.P01
