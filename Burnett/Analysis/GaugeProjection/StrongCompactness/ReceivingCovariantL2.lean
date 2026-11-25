import Burnett.Analysis.GaugeProjection.StrongCompactness.ReceivingCovariantL2Geometry
import Burnett.Analysis.GaugeProjection.StrongCompactness.ReceivingChartGeometricVolume
import Burnett.Geometry.AuxiliaryAdmissibility
import Burnett.Geometry.ManifoldVolumeRegularity

/-! Strong intrinsic convergence controls the actual receiving covariant-gradient input. -/

set_option autoImplicit false
set_option maxRecDepth 4700
set_option maxHeartbeats 4200000

noncomputable section
namespace Burnett.Microlocal.AtlasVolumeGradient

open Set Filter MeasureTheory Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Geometry.IntrinsicDhMeasure (normScalar continuous_normScalar)
open Burnett.Geometry.AuxiliaryAdmissibility (normScalar_nonneg)
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold Topology ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

private theorem eLpNorm_two_pow_eq {X F : Type*} [MeasurableSpace X] [NormedAddCommGroup F]
    (f : X → F) (μ : Measure X) :
    eLpNorm f 2 μ ^ (2 : ℕ) = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℕ) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) ENNReal.ofNat_ne_top]
  have hInner (x : X) : ‖f x‖ₑ ^ (2 : ℝ) = ‖f x‖ₑ ^ (2 : ℕ) := by
    simp
  simp only [ENNReal.toReal_ofNat, hInner]
  rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

omit [IsManifold Model ∞ M] [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] in
/-- The square of the actual half-density is the coordinate density of the original volume. -/
theorem ofReal_fixedHalfDensity_sq (B : Field (M := M)) (c : AtlasChart M) (x : CoordinateSpace) :
    ENNReal.ofReal (fixedHalfDensity B c x) ^ (2 : ℕ) =
      LorentzVolume.density (metricComponents (fixedForm B c)) x := by
  unfold fixedHalfDensity LorentzVolume.density
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2, Real.sq_sqrt (Real.sqrt_nonneg _)]

/-- In a compact chart window, weighting by the actual half-density squares to the same geometric volume. -/
theorem geometric_lintegral_enorm_sq_eq_receiving (B : Field (M := M)) (hB : IsSmooth B)
    (c : AtlasChart M) {S : Set CoordinateSpace} (hS : IsCompact S) (hSt : S ⊆ c.chart.target)
    (N : M → ℝ) (hN : Measurable N) :
    (∫⁻ m in c.chart.symm '' S, ‖N m‖ₑ ^ (2 : ℕ) ∂(ManifoldVolume.geometricMeasure B)) =
      ∫⁻ x in S, ENNReal.ofReal (fixedHalfDensity B c x) ^ (2 : ℕ) *
        ‖N (c.chart.symm x)‖ₑ ^ (2 : ℕ) ∂(volume : Measure CoordinateSpace) := by
  let G := metricComponents (fixedForm B c)
  let w := LorentzVolume.density G
  let f : M → ℝ≥0∞ := fun m => ‖N m‖ₑ ^ (2 : ℕ)
  have hf : Measurable f := hN.enorm.pow_const _
  have hG : ContinuousOn G S := continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k =>
    (fixedForm_components_smooth B hB c j k).continuousOn.mono hSt
  have hw : AEMeasurable w ((volume : Measure CoordinateSpace).restrict S) :=
    LorentzVolume.aemeasurable_density_restrict volume G S hS.measurableSet hG
  change (∫⁻ m in c.chart.symm '' S, f m ∂(ManifoldVolume.geometricMeasure B)) = _
  rw [geometricMeasure_restrict_atlasCompactWindow B c hS hSt, lintegral_map hf (measurable_atlasVolumeInverse c)]
  change (∫⁻ x in S, f (atlasVolumeInverse c x) ∂((volume : Measure CoordinateSpace).withDensity w)) = _
  have hComp : Measurable (fun x => f (atlasVolumeInverse c x)) := hf.comp (measurable_atlasVolumeInverse c)
  rw [restrict_withDensity hS.measurableSet, lintegral_withDensity_eq_lintegral_mul₀ hw hComp.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
  change w x * f (atlasVolumeInverse c x) = _
  simp only [w, G, f, atlasVolumeInverse_of_mem c (hSt hx), ofReal_fixedHalfDensity_sq]

/-- Every smooth actual covariant derivative norm has finite square integral on compact windows. -/
theorem memLp_normScalar_geometric_restrict (r : Metric (M := M))
    (B H : Field (M := M)) (hB : IsSmooth B) (hH : IsSmooth H) {K : Set M} (hK : IsCompact K) :
    MemLp (normScalar r H) 2 ((ManifoldVolume.geometricMeasure B).restrict K) := by
  letI := ManifoldVolumeRegularity.geometricMeasure_isLocallyFiniteMeasure B hB
  have hf := continuous_normScalar r H hH
  exact (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    ((hf.pow 2).continuousOn.integrableOn_compact hK)

/-- One constant controls the ordinary Lebesgue L² norms of all cutoff slots and sequence indices. -/
theorem exists_fixedVolumeCovariantGradientSchwartz_norm_le (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hn : IsNondegenerate B) (c : AtlasChart M) (χ : D)
    (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ c.chart.target) :
    ∃ C > 0, ∀ (n : ℕ) (i : JetSlot),
      ‖(fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n i).toLp 2 volume‖ ≤
        C * (eLpNorm (normScalar r (fun m => g n m - B m)) 2
          ((ManifoldVolume.geometricMeasure B).restrict (c.chart.symm '' tsupport (χ : CoordinateSpace → ℝ)))).toReal := by
  let S := tsupport (χ : CoordinateSpace → ℝ)
  let K := c.chart.symm '' S
  let V := ManifoldVolume.geometricMeasure B
  have hS : IsCompact S := test_compactSupport χ
  have hK : IsCompact K := hS.image_of_continuousOn (c.chart.continuousOn_symm.mono hχ)
  obtain ⟨C, hC, hBound⟩ := exists_fixedVolumeCovariantGradientSchwartz_pointwise_le r B g hB hg hn c χ hχ
  refine ⟨C, hC, fun n i => ?_⟩
  let H : Field (M := M) := fun m => g n m - B m
  let N := normScalar r H
  let u := fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n i
  let w (x : CoordinateSpace) := ENNReal.ofReal (fixedHalfDensity B c x) ^ (2 : ℕ) *
    ‖N (c.chart.symm x)‖ₑ ^ (2 : ℕ)
  let A := ENNReal.ofReal C ^ (2 : ℕ)
  have hH := IntrinsicCov2.isSmooth_difference (g n) B (hg n) hB
  have hN : Measurable N := (continuous_normScalar r H hH).measurable
  have hNfinite := (memLp_normScalar_geometric_restrict r B H hB hH hK).eLpNorm_ne_top
  have hA : A ≠ ⊤ := by dsimp [A]; finiteness
  have hSupport : (∫⁻ x, ‖u x‖ₑ ^ (2 : ℕ) ∂(volume : Measure CoordinateSpace)) =
      ∫⁻ x in S, ‖u x‖ₑ ^ (2 : ℕ) ∂(volume : Measure CoordinateSpace) := by
    rw [← lintegral_indicator hS.measurableSet]
    apply congrArg (lintegral volume)
    funext x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
    · have hu : u x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx
        (fixedVolumeCovariantGradientSchwartz_tsupport r B g hB hg hn c χ hχ n i h))
      rw [indicator_of_notMem hx, hu, enorm_zero, zero_pow two_ne_zero]
  have hComparison : eLpNorm (u : CoordinateSpace → ℂ) 2 volume ^ (2 : ℕ) ≤
      A * eLpNorm N 2 (V.restrict K) ^ (2 : ℕ) := by
    rw [eLpNorm_two_pow_eq, eLpNorm_two_pow_eq, hSupport]
    rw [geometric_lintegral_enorm_sq_eq_receiving B hB c hS hχ N hN]
    change (∫⁻ x in S, ‖u x‖ₑ ^ (2 : ℕ) ∂(volume : Measure CoordinateSpace)) ≤
      A * ∫⁻ x in S, w x ∂(volume : Measure CoordinateSpace)
    rw [← lintegral_const_mul' A w hA]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hS.measurableSet] with x hx
    have hDx : 0 ≤ fixedHalfDensity B c x := Real.sqrt_nonneg _
    have hNx : 0 ≤ N (c.chart.symm x) := normScalar_nonneg r H _
    have hp := ENNReal.ofReal_le_ofReal (hBound n i x hx)
    rw [ofReal_norm, ENNReal.ofReal_mul (mul_nonneg hC.le hDx), ENNReal.ofReal_mul hC.le,
      ← Real.enorm_eq_ofReal hNx] at hp
    simpa only [w, A, mul_pow, mul_assoc] using pow_le_pow_left' hp (2 : ℕ)
  have hFinite : A * eLpNorm N 2 (V.restrict K) ^ (2 : ℕ) ≠ ⊤ := by finiteness
  have hReal := ENNReal.toReal_mono hFinite hComparison
  simp only [A, ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hC.le] at hReal
  change ‖u.toLp 2 volume‖ ≤ C * (eLpNorm N 2 (V.restrict K)).toReal
  rw [SchwartzMap.norm_toLp]
  apply (sq_le_sq₀ ENNReal.toReal_nonneg (mul_nonneg hC.le ENNReal.toReal_nonneg)).mp
  rwa [mul_pow]

/-- Genuine geometric local L² convergence controls every actual receiving cutoff in the region. -/
theorem fixedVolumeCovariantGradientSchwartz_tendsto_zero_of_intrinsicL2 (r : Metric (M := M))
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hn : IsNondegenerate B) (U : Set M)
    (hL2 : ∀ K : Set M, IsCompact K → K ⊆ U →
      Tendsto (fun n => (eLpNorm (normScalar r (fun m => g n m - B m)) 2
        ((ManifoldVolume.geometricMeasure B).restrict K)).toReal) atTop (𝓝 0))
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ c.chart.target)
    (hχU : c.chart.symm '' tsupport (χ : CoordinateSpace → ℝ) ⊆ U) (i : JetSlot) :
    Tendsto (fun n => (fixedVolumeCovariantGradientSchwartz r B g hB hg hn c χ hχ n i).toLp 2 volume)
      atTop (𝓝 0) := by
  obtain ⟨C, _, hC⟩ := exists_fixedVolumeCovariantGradientSchwartz_norm_le r B g hB hg hn c χ hχ
  have hS : IsCompact (tsupport (χ : CoordinateSpace → ℝ)) := test_compactSupport χ
  have hK := hS.image_of_continuousOn (c.chart.continuousOn_symm.mono hχ)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun _ => norm_nonneg _) (fun n => hC n i)
  simpa only [mul_zero] using (tendsto_const_nhds (x := C)).mul (hL2 _ hK hχU)

end Burnett.Microlocal.AtlasVolumeGradient
