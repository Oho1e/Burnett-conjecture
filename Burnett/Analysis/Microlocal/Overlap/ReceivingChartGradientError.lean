import Burnett.Analysis.Microlocal.Overlap.ReceivingChartSourceCutoffs
import Burnett.Analysis.Fourier.SchwartzDensity

/-! Strong error between the actual receiving jet and the transported ordered source jets. -/

set_option autoImplicit false
set_option maxRecDepth 3300
set_option maxHeartbeats 3000000

noncomputable section
namespace Burnett.Microlocal.AtlasVolumeGradient

open Set Filter MeasureTheory Burnett.Geometry Burnett.RicciSymbol Burnett.Fourier
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear ManifoldMetricTransition
open MetricJetNaturality TensorCoordinateChange MaximalChart
open ChartVolume (derivativeMatrix)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D test_memLp)
open scoped Topology Manifold ContDiff BigOperators

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- The exact Jacobian and inverse three-slot rule for the principal part of
one receiving gradient. The remaining Hessian terms are treated separately. -/
theorem orderedSourceJetSum_eq_pullback3 (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (c d : AtlasChart M) (η : D) (i : JetSlot) (a : JetSlot → D)
    (hs : ∀ j, tsupport (a j : CoordinateSpace → ℝ) ⊆ c.chart.target)
    (ha : ∀ j x, x ∈ (c.transition d).source →
      (a j : CoordinateSpace → ℝ) x = (η : CoordinateSpace → ℝ) (c.transition d x) * inverseJetEntry c d i j x)
    (n : ℕ) {x : CoordinateSpace} (hx : x ∈ (c.transition d).source) :
    let e := c.transition d
    let J := derivativeMatrix (fderiv ℝ (d.transition c) (e x))
    let y := e x
    (∑ j : JetSlot, fixedVolumeGradientSchwartz B g hB hg hn c (a j) (hs j) n j x) =
      (((Real.sqrt |(fderiv ℝ e x).det| * ((η : CoordinateSpace → ℝ) y * fixedHalfDensity B d y)) *
        pullback3 J (coordinateJet (fixedPerturbation B (g n) c) x) i.1 i.2.1 i.2.2 : ℝ) : ℂ) := by
  intro e J y
  have hEntry (j : JetSlot) : fixedVolumeGradientSchwartz B g hB hg hn c (a j) (hs j) n j x =
      ((((η : CoordinateSpace → ℝ) y * inverseJetEntry c d i j x * fixedHalfDensity B c x) *
        coordinateJet (fixedPerturbation B (g n) c) x j.1 j.2.1 j.2.2 : ℝ) : ℂ) := by
    rw [fixedVolumeGradientSchwartz_apply, ha j x hx]
  simp only [hEntry, ← Complex.ofReal_sum]
  congr 1
  rw [fixedHalfDensity_change B c d hx, pullback3_apply]
  simp only [Fintype.sum_prod_type, Finset.mul_sum, inverseJetEntry, e, J, y]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- On an actual compact chart overlap the original, volume-weighted receiving
jet differs strongly in L² from the transported finite ordered source sum.
The sequence comes from the original perturbations, with no extraction. -/
theorem fixedVolumeGradient_sub_transportedSourceSum_tendsto_zero
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (c d : AtlasChart M)
    (K : Set CoordinateSpace) (hK : IsCompact K) (hKU : K ⊆ (c.transition d).source)
    (η : D) (hη : tsupport (η : CoordinateSpace → ℝ) ⊆ (c.transition d) '' K)
    (hηd : tsupport (η : CoordinateSpace → ℝ) ⊆ d.chart.target)
    (i : JetSlot) (a : JetSlot → D)
    (hs : ∀ j, tsupport (a j : CoordinateSpace → ℝ) ⊆ c.chart.target)
    (ha : ∀ j x, x ∈ (c.transition d).source →
      (a j : CoordinateSpace → ℝ) x = (η : CoordinateSpace → ℝ) (c.transition d x) * inverseJetEntry c d i j x)
    (v : ℕ → SchwartzMap CoordinateSpace ℂ)
    (hv : ∀ n, tsupport (v n : CoordinateSpace → ℂ) ⊆ (c.transition d) '' K)
    (hV : ∀ n x, x ∈ K → v n (c.transition d x) =
      (Real.sqrt |(fderiv ℝ (c.transition d) x).det|)⁻¹ •
        (∑ j : JetSlot, fixedVolumeGradientSchwartz B g hB hg hn c (a j) (hs j) n j x)) :
    Tendsto (fun n => (fixedVolumeGradientSchwartz B g hB hg hn d η hηd n i).toLp 2 volume -
      (v n).toLp 2 volume) atTop (𝓝 0) := by
  let e := c.transition d
  let U := e '' K
  have hU : IsCompact U := hK.image_of_continuousOn (e.continuousOn.mono hKU)
  have hSymm : e.symm = d.transition c := by
    simp only [e, AtlasChart.transition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  have hUD : U ⊆ (d.transition c).source := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← hSymm]
    exact e.mapsTo (hKU hx)
  have hLeft (x : CoordinateSpace) (hx : x ∈ K) : d.transition c (e x) = x := by
    rw [← hSymm]
    exact e.left_inv (hKU hx)
  let F (n : ℕ) (y : CoordinateSpace) := coordinateJet (fixedPerturbation B (g n) d) y -
    pullback3 (derivativeMatrix (fderiv ℝ (d.transition c) y))
      (coordinateJet (fixedPerturbation B (g n) c) (d.transition c y))
  have hUniform : TendstoUniformlyOn F (fun _ => 0) atTop U :=
    bothCharts_rawJet_error_uniform r B g hB hg hconv d c hU hUD
  let w := fixedWeightedCutoff B hB hn d η hηd
  let z (y : CoordinateSpace) : ℂ := ((w : CoordinateSpace → ℝ) y : ℂ)
  have hz : MemLp z 2 volume := (test_memLp w).ofReal
  let A := ‖hz.toLp z‖
  let u := fixedVolumeGradientSchwartz B g hB hg hn d η hηd
  have hErr (n : ℕ) (y : CoordinateSpace) (hy : y ∈ U) :
      u n i y - v n y = z y * (F n y i.1 i.2.1 i.2.2 : ℂ) := by
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' := hKU hx
    let J := derivativeMatrix (fderiv ℝ (d.transition c) (e x))
    let D₀ := Real.sqrt |(fderiv ℝ e x).det|
    have hp : 0 < D₀ :=
      Real.sqrt_pos.2 (abs_pos.2 (chartDerivative_det_ne_zero c d x hx'))
    have hApprox := hV n x hx
    change v n (e x) = D₀⁻¹ •
      (∑ j : JetSlot, fixedVolumeGradientSchwartz B g hB hg hn c (a j) (hs j) n j x) at hApprox
    rw [orderedSourceJetSum_eq_pullback3 B g hB hg hn c d η i a hs ha n hx'] at hApprox
    change v n (e x) = D₀⁻¹ •
      ((((D₀ * ((η : CoordinateSpace → ℝ) (e x) * fixedHalfDensity B d (e x))) *
        pullback3 J (coordinateJet (fixedPerturbation B (g n) c) x) i.1 i.2.1 i.2.2 : ℝ) : ℂ)) at hApprox
    rw [Complex.real_smul, ← Complex.ofReal_mul] at hApprox
    simp only [← mul_assoc, inv_mul_cancel₀ hp.ne', one_mul] at hApprox
    rw [hApprox]
    dsimp only [u, z, w, fixedWeightedCutoff, F, Pi.sub_apply]
    rw [fixedVolumeGradientSchwartz_apply, hLeft x hx]
    simp only [J, Complex.ofReal_sub, Complex.ofReal_mul, mul_sub]
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (A + 1)
  have hδ : 0 < δ := div_pos hε (by dsimp [A]; positivity)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hUniform δ hδ] with n hn'
  have hLocal : ∀ y, ‖u n i y - v n y‖ ≤ δ * ‖z y‖ := by
    intro y
    by_cases hy : y ∈ U
    · have hs' : ‖F n y‖ < δ := by simpa only [dist_zero_left] using hn' y hy
      have he : ‖F n y i.1 i.2.1 i.2.2‖ ≤ ‖F n y‖ :=
        (norm_le_pi_norm (F n y i.1 i.2.1) i.2.2).trans
          ((norm_le_pi_norm (F n y i.1) i.2.1).trans (norm_le_pi_norm (F n y) i.1))
      rw [hErr n y hy, norm_mul, Complex.norm_real, mul_comm δ]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      simpa only [Complex.norm_real] using he.trans hs'.le
    · have hU0 : u n i y = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hy (hη ((fixedVolumeGradientSchwartz_tsupport B g hB hg hn d η hηd n i) h)))
      have hV0 : v n y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hv n h))
      simp only [hU0, hV0, sub_zero, norm_zero]
      exact mul_nonneg hδ.le (norm_nonneg _)
  have hBound := norm_toLp_le_of_norm_le (((u n i).memLp 2 volume).sub ((v n).memLp 2 volume)) hz hδ.le hLocal
  rw [MemLp.toLp_sub] at hBound
  change ‖(u n i).toLp 2 volume - (v n).toLp 2 volume‖ ≤ δ * A at hBound
  rw [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)]
  apply hBound.trans_lt
  calc
    δ * A < δ * (A + 1) := mul_lt_mul_of_pos_left (lt_add_one A) hδ
    _ = ε := div_mul_cancel₀ ε (by dsimp [A]; positivity)

end Burnett.Microlocal.AtlasVolumeGradient
