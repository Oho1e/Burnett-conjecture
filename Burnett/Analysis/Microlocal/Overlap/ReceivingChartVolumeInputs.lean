import Burnett.Analysis.Microlocal.Overlap.ReceivingChartRawJet

/-! The original volume half-density gradients in every compatible smooth chart. -/

set_option autoImplicit false
set_option maxRecDepth 3100
set_option maxHeartbeats 2300000

noncomputable section
namespace Burnett.Microlocal.AtlasVolumeGradient

open Set Filter MeasureTheory Burnett.RicciSymbol Burnett.Fourier
open Burnett.Geometry ConnectionDifference ConnectionCoordinateChange ManifoldMetric ManifoldMetricSequence
open ManifoldBilinear ChartVolume ManifoldMetricTransition MetricJetNaturality TensorCoordinateChange MaximalChart
open Burnett.F05.CoordinateCurl Burnett.F05.ChartVolumeBridge Burnett.F05.OverlapCovariantGradient
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet
open scoped Manifold ContDiff Topology BigOperators InnerProduct

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

def fixedHalfDensity (B : ManifoldBilinear.Field (M := M)) (c : AtlasChart M) (x : CoordinateSpace) : ℝ :=
  Real.sqrt (Real.sqrt |Matrix.det (metricComponents (fixedForm B c) x)|)


theorem fixedHalfDensity_eq_preferred (B : Field (M := M)) (q : M)
    {x : CoordinateSpace} (hx : x ∈ (chartAt CoordinateSpace q).target) :
    fixedHalfDensity B (.atPoint q) x = chartHalfDensity B q x := by
  unfold fixedHalfDensity chartHalfDensity
  rw [fixedForm_eq_preferred_components B q hx]

theorem fixedHalfDensity_change (B : ManifoldBilinear.Field (M := M)) (c d : AtlasChart M)
    {x : CoordinateSpace} (hx : x ∈ (c.transition d).source) :
    fixedHalfDensity B c x = Real.sqrt |(fderiv ℝ (c.transition d) x).det| * fixedHalfDensity B d (c.transition d x) := by
  unfold fixedHalfDensity
  rw [fixedForm_matrix_change B c d hx,TensorCoordinateChange.pullbackMetric,
    LorentzVolume.sqrt_abs_det_pullback,det_derivativeMatrix,Real.sqrt_mul (abs_nonneg _)]

variable [SecondCountableTopology M]

theorem fixedHalfDensity_smooth (B : ManifoldBilinear.Field (M := M)) (hs : ManifoldBilinear.IsSmooth B)
    (hn : ManifoldBilinear.IsNondegenerate B) (c : AtlasChart M) :
    ContDiffOn ℝ ∞ (fixedHalfDensity B c) c.chart.target := by
  let D₀ (x : CoordinateSpace) := Matrix.det (metricComponents (fixedForm B c) x)
  have hD : ContDiffOn ℝ ∞ D₀ c.chart.target :=
    SmoothMetricConnection.contDiffOn_det _ _ (fixedForm_components_smooth B hs c)
  have hne (x : CoordinateSpace) (hx : x ∈ c.chart.target) : D₀ x ≠ 0 := by
    exact fixedForm_det_ne_zero B hn c hx
  have ha := hD.abs hne
  exact (ha.sqrt (fun x hx => abs_ne_zero.mpr (hne x hx))).sqrt
    (fun x hx => (Real.sqrt_pos.mpr (abs_pos.mpr (hne x hx))).ne')

def fixedWeightedCutoff (B : ManifoldBilinear.Field (M := M)) (hs : ManifoldBilinear.IsSmooth B)
    (hn : ManifoldBilinear.IsNondegenerate B) (c : AtlasChart M) (χ : D)
    (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ c.chart.target) : D :=
  ⟨fun x => (χ : CoordinateSpace → ℝ) x * fixedHalfDensity B c x,
    ⟨Burnett.Analysis.LocalWeakDerivative.contDiff_test_mul_local c.chart.open_target
      (test_smooth χ) hχ (fixedHalfDensity_smooth B hs hn c), (test_compactSupport χ).mul_right⟩⟩

def fixedComponent (B : Field (M := M)) (g : ℕ → Field (M := M)) (c : AtlasChart M)
    (n : ℕ) (p : TensorPair) (x : CoordinateSpace) : ℝ := fixedPerturbation B (g n) c x p.1 p.2

theorem fixedComponent_smooth (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B)
    (hg : ∀ n, IsSmooth (g n)) (c : AtlasChart M) (n : ℕ) (p : TensorPair) :
    ContDiffOn ℝ ∞ (fixedComponent B g c n p) c.chart.target :=
  (fixedForm_components_smooth (g n) (hg n) c p.1 p.2).sub (fixedForm_components_smooth B hB c p.1 p.2)

theorem fixedComponent_localUniform (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hconv : LocallyUniformlyConverges r g B) (c : AtlasChart M) (p : TensorPair)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hU : K ⊆ c.chart.target) :
    TendstoUniformlyOn (fun n => fixedComponent B g c n p) (fun _ => 0) atTop K := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have ht := fixed_components_uniform_of_physical_C0loc r g B hconv c K hK hU
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp ht ε hε] with n hn
  intro x hx
  let A := fixedPerturbation B (g n) c x
  have hs : ‖A‖ < ε := by
    have hh := hn x hx
    rw [dist_comm,dist_eq_norm] at hh
    exact hh
  exact (show dist 0 (fixedComponent B g c n p x) = ‖A p.1 p.2‖ from dist_zero_left _).trans_lt
    (((norm_le_pi_norm (A p.1) p.2).trans (norm_le_pi_norm A p.1)).trans_lt hs)

def fixedGradientSchwartz (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (c : AtlasChart M)
    (η : D) (hη : tsupport (η : CoordinateSpace → ℝ) ⊆ c.chart.target) (n : ℕ) (i : JetSlot) :
    SchwartzMap CoordinateSpace ℂ :=
  tensorGradientSchwartz c.chart.open_target η hη (fixedComponent B g c) (fixedComponent_smooth B g hB hg c) n i

theorem fixedGradientSchwartz_apply (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (c : AtlasChart M)
    (η : D) (hη : tsupport (η : CoordinateSpace → ℝ) ⊆ c.chart.target)
    (n : ℕ) (i : JetSlot) (x : CoordinateSpace) :
    fixedGradientSchwartz B g hB hg c η hη n i x =
      (((η : CoordinateSpace → ℝ) x * coordinateJet (fixedPerturbation B (g n) c) x i.1 i.2.1 i.2.2 : ℝ) : ℂ) := rfl


/-- The actual localized derivative of the original perturbation, using the
background volume half-density in an arbitrary smooth atlas chart. -/
def fixedVolumeGradientSchwartz (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ c.chart.target)
    (n : ℕ) (i : JetSlot) : SchwartzMap CoordinateSpace ℂ :=
  let w := fixedWeightedCutoff B hB hn c χ hχ
  let hw : tsupport (w : CoordinateSpace → ℝ) ⊆ c.chart.target := tsupport_mul_subset_left.trans hχ
  fixedGradientSchwartz B g hB hg c w hw n i

theorem fixedVolumeGradientSchwartz_apply (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ c.chart.target)
    (n : ℕ) (i : JetSlot) (x : CoordinateSpace) :
    fixedVolumeGradientSchwartz B g hB hg hn c χ hχ n i x =
      (((χ : CoordinateSpace → ℝ) x * fixedHalfDensity B c x *
        coordinateJet (fixedPerturbation B (g n) c) x i.1 i.2.1 i.2.2 : ℝ) : ℂ) := rfl

theorem fixedVolumeGradientSchwartz_tsupport (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ c.chart.target)
    (n : ℕ) (i : JetSlot) :
    tsupport (fixedVolumeGradientSchwartz B g hB hg hn c χ hχ n i : CoordinateSpace → ℂ) ⊆
      tsupport (χ : CoordinateSpace → ℝ) := by
  apply closure_mono
  intro x hx
  by_contra h
  have hz : χ.val x = 0 := by simpa [Function.mem_support] using h
  exact hx (by rw [fixedVolumeGradientSchwartz_apply, hz, zero_mul, zero_mul, Complex.ofReal_zero])

omit [SecondCountableTopology M] in
theorem fixedPerturbation_jet_eq_preferred (B g : Field (M := M)) (q : M)
    {x : CoordinateSpace} (hx : x ∈ (chartAt CoordinateSpace q).target) :
    coordinateJet (fixedPerturbation B g (.atPoint q)) x =
      coordinateJet (fun y => metricComponents (coordinateBilinear g q) y -
        metricComponents (coordinateBilinear B q) y) x := by
  funext b i j
  have he : (fun y => fixedPerturbation B g (.atPoint q) y i j) =ᶠ[𝓝 x]
      (fun y => (metricComponents (coordinateBilinear g q) y -
        metricComponents (coordinateBilinear B q) y) i j) := by
    filter_upwards [(chartAt CoordinateSpace q).open_target.mem_nhds hx] with y hy
    simp only [fixedPerturbation, Pi.sub_apply, fixedForm_eq_preferred_components _ _ hy]
  exact congrArg (fun L : CoordinateSpace →L[ℝ] ℝ => L _) he.fderiv_eq

theorem fixedVolumeGradientSchwartz_eq_preferred (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B) (q : M)
    (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace q).target)
    (n : ℕ) (i : JetSlot) :
    fixedVolumeGradientSchwartz B g hB hg hn (.atPoint q) χ hχ n i =
      originalVolumeGradientSchwartz B g hB hg hn q χ hχ n i := by
  apply SchwartzMap.ext
  intro x
  rw [fixedVolumeGradientSchwartz_apply, originalVolumeGradientSchwartz,
    Burnett.F05.OriginalCoordinateCurl.originalGradientSchwartz_apply_rawJet, chartVolumeWeightedCutoff_apply]
  by_cases hx : x ∈ tsupport (χ : CoordinateSpace → ℝ)
  · rw [fixedHalfDensity_eq_preferred B q (hχ hx), fixedPerturbation_jet_eq_preferred B (g n) q (hχ hx)]
  · simp only [image_eq_zero_of_notMem_tsupport hx, zero_mul]

end Burnett.Microlocal.AtlasVolumeGradient
