import Burnett.Analysis.Microlocal.Overlap.ReceivingChartVolumeInputs
import Burnett.Analysis.Microlocal.Overlap.OriginalWeakInput
import Burnett.Analysis.Microlocal.BesselLocalization

/-! Bounded weak-null receiving gradients with the actual local metric data. -/

set_option autoImplicit false
set_option maxRecDepth 3100
set_option maxHeartbeats 2300000

noncomputable section
namespace Burnett.Microlocal.AtlasVolumeGradient

open Set Filter MeasureTheory Burnett.RicciSymbol Burnett.Fourier
open Burnett.Geometry ConnectionDifference ConnectionCoordinateChange ManifoldMetric ManifoldMetricSequence
open ManifoldBilinear ChartVolume ManifoldMetricTransition MetricJetNaturality TensorCoordinateChange MaximalChart
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open Burnett.Microlocal.Overlap (sourceSchwartz_weakL2_zero)
open Burnett.Microlocal.BesselLocalization (coeffMul)
open Burnett.F05.OriginalCoordinateCurl (exists_rawComponentDerivative_bound_of_original)
open Burnett.F05.CoordinateCurl Burnett.F05.ChartVolumeBridge Burnett.F05.OverlapCovariantGradient
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet
open scoped Manifold ContDiff Topology BigOperators InnerProduct

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

omit [IsManifold Model ∞ M] in
theorem pullback3_continuousOn_transition (c d : AtlasChart M) :
    ContinuousOn (fun z : CoordinateSpace × FirstJet =>
      pullback3 (derivativeMatrix (fderiv ℝ (c.transition d) z.1)) z.2)
      ((c.transition d).source ×ˢ univ) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  apply continuousOn_pi.mpr
  intro k
  simp only [pullback3_apply]
  have hA (a b : Index) := (fixedJacobian_entry_smooth c d a b).continuousOn.comp
    (continuous_fst : Continuous (Prod.fst : CoordinateSpace × FirstJet → CoordinateSpace)).continuousOn
    (show MapsTo Prod.fst ((c.transition d).source ×ˢ (univ : Set FirstJet)) (c.transition d).source from
      fun _ hz => hz.1)
  apply continuousOn_finset_sum
  intro a _
  apply continuousOn_finset_sum
  intro b _
  apply continuousOn_finset_sum
  intro f _
  exact (((hA a i).mul (hA b j)).mul (hA f k)).mul (by fun_prop)

variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

theorem fixedJet_uniform_bound_of_original_on_overlap
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B)
    (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (q : M) {K : Set CoordinateSpace}
    (hK : IsCompact K) (hKU : K ⊆ (c.transition (.atPoint q)).source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ K → ‖coordinateJet (fixedPerturbation B (g n) c) x‖ ≤ C := by
  let d := AtlasChart.atPoint q
  let e := c.transition d
  let L (n : ℕ) := coordinateJet (fixedPerturbation B (g n) c)
  let J (n : ℕ) := coordinateJet (fixedPerturbation B (g n) d)
  let P (z : CoordinateSpace × FirstJet) := pullback3 (derivativeMatrix (fderiv ℝ e z.1)) z.2
  have hI : IsCompact (e '' K) := hK.image_of_continuousOn (e.continuousOn.mono hKU)
  have ht : e '' K ⊆ (chartAt CoordinateSpace q).target := image_subset_iff.mpr fun _ hx => (e.mapsTo (hKU hx)).1
  obtain ⟨A,hA,hj⟩ := exists_rawComponentDerivative_bound_of_original r B g hB hg hn hconv hb q _ hI ht
  have hJ (n : ℕ) (x : CoordinateSpace) (hx : x ∈ K) : ‖J n (e x)‖ ≤ A := by
    dsimp only [J]
    rw [fixedPerturbation_jet_eq_preferred B (g n) q (ht (mem_image_of_mem _ hx))]
    apply (pi_norm_le_iff_of_nonneg hA).mpr
    intro b
    apply (pi_norm_le_iff_of_nonneg hA).mpr
    intro i
    apply (pi_norm_le_iff_of_nonneg hA).mpr
    intro j
    exact hj n (i,j) b (e x) (mem_image_of_mem _ hx)
  let V := Metric.closedBall (0 : FirstJet) A
  have hV : IsCompact V := isCompact_closedBall _ _
  have hP : ContinuousOn P (K ×ˢ V) := (pullback3_continuousOn_transition c d).mono
    (fun _ hz => ⟨hKU hz.1, mem_univ _⟩)
  obtain ⟨D,hD,hbound⟩ := ((hK.prod hV).image_of_continuousOn hP).isBounded.exists_pos_norm_le
  have he := bothCharts_rawJet_error_uniform r B g hB hg hconv c d hK hKU
  have htail : ∀ᶠ n in atTop, ∀ x ∈ K, ‖L n x‖ ≤ 1 + D := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp he 1 zero_lt_one] with n hh
    intro x hx
    have hl : ‖L n x - P (x,J n (e x))‖ ≤ 1 := by simpa only [dist_zero_left] using (hh x hx).le
    have hmem : J n (e x) ∈ V := by simpa only [V,Metric.mem_closedBall,dist_zero_right] using hJ n x hx
    have hp := hbound (P (x,J n (e x))) (mem_image_of_mem P (show (x,J n (e x)) ∈ K ×ˢ V from ⟨hx,hmem⟩))
    exact (norm_le_norm_sub_add _ _).trans (add_le_add hl hp)
  apply Burnett.Analysis.GeometricHminusBoundedForcing.all_bound_of_eventual_on_compact L K hK _ (by positivity : 0 ≤ 1 + D) htail
  intro n
  apply (BackgroundConnection.continuousOn_coordinateJet _ c.chart.target c.chart.open_target ?_).mono (fun _ hx => (hKU hx).1)
  intro i j
  exact ((fixedForm_components_smooth (g n) (hg n) c i j).sub (fixedForm_components_smooth B hB c i j)).of_le (by
    change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)

theorem fixedJet_uniform_bound_on_compact
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B)
    (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) {K : Set CoordinateSpace}
    (hK : IsCompact K) (hU : K ⊆ c.chart.target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ K → ‖coordinateJet (fixedPerturbation B (g n) c) x‖ ≤ C := by
  classical
  let J (n : ℕ) := coordinateJet (fixedPerturbation B (g n) c)
  have hgerm (x : K) : ∃ (U : Set CoordinateSpace) (A : ℝ),
      U ∈ 𝓝 (x : CoordinateSpace) ∧ 0 ≤ A ∧ ∀ n y, y ∈ U → ‖J n y‖ ≤ A := by
    let q := c.chart.symm x
    let e := c.transition (.atPoint q)
    have he : (x : CoordinateSpace) ∈ e.source := ⟨hU x.2, mem_chart_source CoordinateSpace q⟩
    obtain ⟨U,hUc,hx,hUe⟩ := exists_compact_subset e.open_source he
    obtain ⟨A,hA,hj⟩ := fixedJet_uniform_bound_of_original_on_overlap r B g hB hg hn hconv hb c q hUc hUe
    exact ⟨U,A,mem_interior_iff_mem_nhds.mp hx,hA,hj⟩
  choose U A hu ha hj using hgerm
  obtain ⟨t,ht⟩ := hK.elim_nhds_subcover' (fun x hx => U ⟨x,hx⟩) (fun x hx => hu ⟨x,hx⟩)
  refine ⟨∑ z ∈ t, A z, Finset.sum_nonneg (fun z _ => ha z),?_⟩
  intro n y hy
  obtain ⟨x,hxt,hxy⟩ := mem_iUnion₂.mp (ht hy)
  exact (hj x n y hxy).trans (Finset.single_le_sum (fun z _ => ha z) hxt)


omit [MeasurableSpace M] [BorelSpace M] in
theorem coeffMul_fixedVolumeGradientSchwartz (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (c : AtlasChart M) (χ η : D) (hη : tsupport (η : CoordinateSpace → ℝ) ⊆ c.chart.target)
    (n : ℕ) (i : JetSlot) :
    let t : D := ⟨fun x : CoordinateSpace => (χ : CoordinateSpace → ℝ) x * (η : CoordinateSpace → ℝ) x,
      (test_smooth χ).mul (test_smooth η), (test_compactSupport χ).mul_right⟩
    let ht := (tsupport_mul_subset_right : tsupport (t : CoordinateSpace → ℝ) ⊆ tsupport (η : CoordinateSpace → ℝ)).trans hη
    coeffMul χ (fixedVolumeGradientSchwartz B g hB hg hn c η hη n i) =
      fixedVolumeGradientSchwartz B g hB hg hn c t ht n i := by
  intro t ht
  apply SchwartzMap.ext
  intro x
  change ((χ : CoordinateSpace → ℝ) x : ℂ) * fixedVolumeGradientSchwartz B g hB hg hn c η hη n i x =
    fixedVolumeGradientSchwartz B g hB hg hn c t ht n i x
  rw [fixedVolumeGradientSchwartz_apply, fixedVolumeGradientSchwartz_apply]
  change _ = (((χ : CoordinateSpace → ℝ) x * (η : CoordinateSpace → ℝ) x * _ *
    coordinateJet (fixedPerturbation B (g n) c) x i.1 i.2.1 i.2.2 : ℝ) : ℂ)
  push_cast
  ring

/-- Every compactly localized receiving-chart jet has a uniform true L²
bound and is weakly null along the original sequence. -/
theorem fixedVolumeGradient_weak_and_uniform_L2
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ c.chart.target) :
    let u := fixedVolumeGradientSchwartz B g hB hg hn c χ hχ
    ∃ C : ℝ, 0 ≤ C ∧ (∀ n i, ‖(u n i).toLp 2 volume‖ ≤ C) ∧
      ∀ i (v : ComplexL2 CoordinateSpace), Tendsto (fun n => inner ℂ v ((u n i).toLp 2 volume)) atTop (𝓝 0) := by
  intro u
  let w := fixedWeightedCutoff B hB hn c χ hχ
  have hwS : tsupport (w : CoordinateSpace → ℝ) ⊆ tsupport (χ : CoordinateSpace → ℝ) :=
    tsupport_mul_subset_left
  have hw := hwS.trans hχ
  obtain ⟨A, hA, hj⟩ := fixedJet_uniform_bound_on_compact r B g hB hg hn hconv hb c
    (test_compactSupport w) hw
  let z (x : CoordinateSpace) : ℂ := ((w : CoordinateSpace → ℝ) x : ℂ)
  have hz : MemLp z 2 volume := (test_memLp w).ofReal
  let C := A * ‖hz.toLp z‖
  have hC : 0 ≤ C := mul_nonneg hA (norm_nonneg _)
  have hU (n : ℕ) (i : JetSlot) : ‖(u n i).toLp 2 volume‖ ≤ C := by
    apply norm_toLp_le_of_norm_le ((u n i).memLp 2 volume) hz hA
    intro x
    change ‖(((w : CoordinateSpace → ℝ) x *
      coordinateJet (fixedPerturbation B (g n) c) x i.1 i.2.1 i.2.2 : ℝ) : ℂ)‖ ≤ A * ‖z x‖
    rw [Complex.norm_real, norm_mul, mul_comm A]
    by_cases hx : x ∈ tsupport (w : CoordinateSpace → ℝ)
    · let J := coordinateJet (fixedPerturbation B (g n) c) x
      have hi : ‖J i.1 i.2.1 i.2.2‖ ≤ A :=
        (norm_le_pi_norm (J i.1 i.2.1) i.2.2).trans
          ((norm_le_pi_norm (J i.1) i.2.1).trans ((norm_le_pi_norm J i.1).trans (hj n x hx)))
      simpa only [z, Complex.norm_real] using
        mul_le_mul_of_nonneg_left hi (norm_nonneg ((w : CoordinateSpace → ℝ) x))
    · simp [z, image_eq_zero_of_notMem_tsupport hx]
  refine ⟨C, hC, hU, ?_⟩
  intro i v
  let f (n : ℕ) := localizedGradientTest c.chart.open_target w hw
    (fixedComponent_smooth B g hB hg c n i.2) i.1
  obtain ⟨θ, hθ⟩ := exists_outerCutoff_on_tsupport w
  have hOne (n : ℕ) (x : CoordinateSpace) (hx : (f n : CoordinateSpace → ℝ) x ≠ 0) :
      (θ : CoordinateSpace → ℝ) x = 1 :=
    hθ x (localizedGradient_tsupport w (fixedComponent B g c n i.2) i.1 (subset_tsupport _ hx))
  have hEq (n : ℕ) : sourceSchwartz (test_smooth (f n)) θ (hOne n) = u n i := by
    exact SchwartzMap.ext fun _ => rfl
  have hTest := localizedGradientTest_test_tendsto_zero c.chart.open_target w hw
    (fun n => fixedComponent B g c n i.2) (fun n => fixedComponent_smooth B g hB hg c n i.2)
    (fixedComponent_localUniform r B g hconv c i.2) i.1
  have hWeak := sourceSchwartz_weakL2_zero (fun n => (f n : CoordinateSpace → ℝ))
    (fun n => test_smooth (f n)) θ hOne C hC (fun n => by rw [hEq n]; exact hU n i) hTest v
  simpa only [hEq] using hWeak

end Burnett.Microlocal.AtlasVolumeGradient
