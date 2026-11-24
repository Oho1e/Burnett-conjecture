import Burnett.Analysis.Microlocal.Overlap.ReceivingChartRoundFrequency
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartMovedSymbols
import Burnett.Analysis.Microlocal.Overlap.GlobalReceivingChartJetMeasure

/-! Identify the finite sum of weighted source pairings with the
receiving phase integral of the same original covariance. -/

set_option autoImplicit false
set_option maxHeartbeats 4300000
set_option maxRecDepth 3200

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Filter MeasureTheory Set Burnett.Fourier Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open UnitCosphere (Cosphere projection)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AtlasOverlapKernel (inverseJetEntry inverseJetEntry_eq_tensorJetTransition
  receivingFrequency receivingFrequency_eq_fixedCotangentTransition_mulVec
  chartTransitionFrequency_eq_frozen movingChartAngularSymbol movingChartAngularSymbol_norm_le)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.FixedChartGeometricDensity (roundCovector)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density integrable_density_entry)
open Burnett.X02.SobolevTestJet (D test_smooth)
open scoped BigOperators ComplexConjugate ContDiff Manifold Matrix Topology

local notation "E" => CoordinateSpace
variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

private theorem sourcePoint_in_chart (r : Metric (M := M)) (q : CompactChartInput M)
    (z : Chart q.ball) :
    projection (chartAuxiliaryCosphere r q z) ∈ (chartAt E q.center).source :=
  (chartAt E q.center).symm_mapsTo (q.ball_in_chart z.1.property)

private theorem sourcePoint_coordinates (r : Metric (M := M)) (q : CompactChartInput M)
    (z : Chart q.ball) : chartAt E q.center (projection (chartAuxiliaryCosphere r q z)) = z.1 :=
  (chartAt E q.center).right_inv (q.ball_in_chart z.1.property)

/-- Evaluating a degree-zero target multiplier on the round target code is
exactly evaluation at the true inverse-adjoint image of the source ray. -/
theorem receivingFourier_mode_eq_roundPhase (r : Metric (M := M)) (q : CompactChartInput M)
    (d : AtlasChart M) (z : Chart q.ball)
    (hd : projection (chartAuxiliaryCosphere r q z) ∈ d.chart.source)
    (m : BoundedSymbol E) (hm : DegreeZero (m : E → ℂ)) :
    let c := AtlasChart.atPoint q.center
    let Θ := atlasAngularPhaseCode d (chartAuxiliaryCosphere r q z)
    Θ.1 = c.transition d z.1 ∧ m Θ.2.val = m (receivingFrequency c d z.1 z.2.val) := by
  intro c Θ
  let x := projection (chartAuxiliaryCosphere r q z)
  have hc := sourcePoint_in_chart r q z
  have hcx : c.chart x = z.1 := sourcePoint_coordinates r q z
  have htr : c.transition d z.1 = d.chart x := by
    rw [← hcx]
    change d.chart (c.chart.symm (c.chart x)) = d.chart x
    rw [c.chart.left_inv hc]
  have hz : z.1.val ∈ (c.transition d).source := ⟨q.ball_in_chart z.1.property, hd⟩
  have hF := receivingFrequency_eq_fixedCotangentTransition_mulVec c d hc z.2.val
  rw [hcx] at hF
  change receivingFrequency c d z.1 z.2.val =
    WithLp.toLp 2 (Burnett.F07.IntrinsicAmplitudeCoordinates.fixedCotangentTransitionMatrix c d x *ᵥ
      roundCovector z) at hF
  have hNorm : ‖z.2.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using z.2.property
  have he : receivingFrequency c d z.1 z.2.val ≠ 0 := by
    rw [chartTransitionFrequency_eq_frozen c d hz]
    let L := AtlasOverlapKernel.frozenChartFrequency c d hz
    intro hZero
    exact (norm_ne_zero_iff.mp (hNorm.symm ▸ one_ne_zero))
      (L.injective (hZero.trans (map_zero L).symm))
  dsimp only [Θ]
  rw [atlasAngularPhaseCode_receiving_ray r q d z hd, ← hF, htr]
  refine ⟨rfl, ?_⟩
  rw [atlasAngularDirection_value he]
  exact hm _ (inv_pos.mpr (norm_pos_iff.mpr he)) _

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- On one compact overlap, the separated receiving test is the sum of the
ordered source pairings with its two real cutoff quotients. -/
theorem receivingWindow_integral_eq_sourceAngularSum
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalAmplitudeChartLaws r B g hB hg hnB σ A)
    (q : CompactChartInput M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    (d : AtlasChart M) {K : Set M} (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus ∩ d.chart.source)
    (η₀ η₁ : D) (i j : JetSlot) (α β : JetSlot → D)
    (a b m : BoundedSymbol E) (hBmeas : Measurable (b : E → ℂ))
    (hAmeas : Measurable (movingChartAngularSymbol (.atPoint q.center) d a m))
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (hDegree : DegreeZero (m : E → ℂ))
    (hαS : ∀ k, tsupport (α k : E → ℝ) ⊆ (chartAt E q.center) '' K)
    (hPull : ∀ x ∈ (chartAt E q.center) '' K, a x = b ((AtlasChart.atPoint q.center).transition d x))
    (hα : ∀ k x, x ∈ (chartAt E q.center) '' K →
      (α k : E → ℝ) x = (η₀ : E → ℝ) ((AtlasChart.atPoint q.center).transition d x) *
        ((q.cutoff : E → ℝ) x)⁻¹ * inverseJetEntry (.atPoint q.center) d i k x)
    (hβ : ∀ l x, x ∈ (chartAt E q.center) '' K →
      (β l : E → ℝ) x = (η₁ : E → ℝ) ((AtlasChart.atPoint q.center).transition d x) *
        ((q.cutoff : E → ℝ) x)⁻¹ * inverseJetEntry (.atPoint q.center) d j l x) :
    let c := AtlasChart.atPoint q.center
    let T (z : AtlasAngularPhase) := (physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) *
      b z.1 * m z.2.val
    (∑ k : JetSlot, ∑ l : JetSlot, ∫ z : Chart q.ball,
      ((physicalCoefficient (α k) z.1 * physicalCoefficient (β l) z.1) *
        movingChartAngularSymbol c d a m (z.1,z.2.val)) * density ν hf z k l ∂traceMeasure ν) =
      ∫ p, T (atlasAngularPhaseCode d p) * atlasOrderedJetEntry d A.density p i j
        ∂A.control.restrict (amplitudeCosphereWindow r K) := by
  intro c T
  let φ := chartAuxiliaryCosphere r q
  let Θ := atlasAngularPhaseCode (r := r) d
  let U := amplitudeChartWindow r q K
  let p (z : Chart q.ball) := movingChartAngularSymbol c d a m (z.1,z.2.val)
  let F (k l : JetSlot) (z : Chart q.ball) :=
    ((physicalCoefficient (α k) z.1 * physicalCoefficient (β l) z.1) * p z) *
      density ν hf z k l
  have hmMeas : Measurable (m : E → ℂ) :=
    measurable_of_continuousOn_compl_singleton 0 hm.continuousOn
  have hcM (c₀ : D) : Measurable (physicalCoefficient c₀ : E → ℂ) :=
    (Complex.ofRealCLM.contDiff.comp (test_smooth c₀)).continuous.measurable
  have hT : Measurable T :=
    (((hcM η₀).comp measurable_fst).mul ((hcM η₁).comp measurable_fst)).mul
      (hBmeas.comp measurable_fst) |>.mul (hmMeas.comp (measurable_subtype_coe.comp measurable_snd))
  let D₀ := ((physicalCoefficient η₀).bound * (physicalCoefficient η₁).bound) * b.bound * m.bound
  have hD₀ : 0 ≤ D₀ := mul_nonneg (mul_nonneg
    (mul_nonneg (physicalCoefficient η₀).bound_nonneg (physicalCoefficient η₁).bound_nonneg) b.bound_nonneg)
    m.bound_nonneg
  have hTB (z : AtlasAngularPhase) : ‖T z‖ ≤ D₀ := by
    simp only [T, norm_mul, D₀]
    have h₀ := (physicalCoefficient η₀).bound_nonneg
    have h₁ := (physicalCoefficient η₁).bound_nonneg
    exact mul_le_mul
      (mul_le_mul
        (mul_le_mul ((physicalCoefficient η₀).norm_le _) ((physicalCoefficient η₁).norm_le _)
          (norm_nonneg _) h₀)
        (b.norm_le _) (norm_nonneg _) (mul_nonneg h₀ h₁))
      (m.norm_le _) (norm_nonneg _) (mul_nonneg (mul_nonneg h₀ h₁) b.bound_nonneg)
  have hBorel := (original_receivingAtlasJetEntry_angularMeasure_on_compact r B g hB hg hsB hsG hnB hnG
    hconv hb hv σ hσ A hA q ν hf hRep d hK hSub i j).2.2.2.2 T hT D₀ hD₀ hTB
  rw [hBorel.2]
  change (∑ k : JetSlot, ∑ l : JetSlot, ∫ z, F k l z ∂traceMeasure ν) =
    ∫ z in U, T (Θ (φ z)) * (chartInverseCutoffComplexSquare q z * receivedOriginalJetDensity r q d ν hf z i j)
      ∂traceMeasure ν
  have hInt (k l : JetSlot) : Integrable (F k l) (traceMeasure ν) := by
    apply (integrable_density_entry ν hf k l).bdd_mul
    · exact ((((hcM (α k)).comp (measurable_subtype_coe.comp measurable_fst)).mul
        ((hcM (β l)).comp (measurable_subtype_coe.comp measurable_fst))).mul
        (hAmeas.comp ((measurable_subtype_coe.comp measurable_fst).prodMk
          (measurable_subtype_coe.comp measurable_snd)))).aestronglyMeasurable
    · refine ⟨(physicalCoefficient (α k)).bound * (physicalCoefficient (β l)).bound * (a.bound * m.bound), fun z => ?_⟩
      simp only [norm_mul]
      exact mul_le_mul
        (mul_le_mul ((physicalCoefficient (α k)).norm_le _) ((physicalCoefficient (β l)).norm_le _)
          (norm_nonneg _) (physicalCoefficient (α k)).bound_nonneg)
        (movingChartAngularSymbol_norm_le c d a m (z.1,z.2.val)) (norm_nonneg _)
        (mul_nonneg (physicalCoefficient (α k)).bound_nonneg (physicalCoefficient (β l)).bound_nonneg)
  have hSum (k : JetSlot) : (∑ l : JetSlot, ∫ z, F k l z ∂traceMeasure ν) =
      ∫ z, ∑ l : JetSlot, F k l z ∂traceMeasure ν := by
    exact (integral_finset_sum Finset.univ (fun l _ => hInt k l)).symm
  simp_rw [hSum]
  rw [← integral_finset_sum Finset.univ
    (fun k _ => integrable_finset_sum Finset.univ (fun l _ => hInt k l))]
  have hUm : MeasurableSet U :=
    hK.isClosed.measurableSet.preimage (continuous_amplitudeChartBase r q).measurable
  rw [← integral_indicator hUm]
  apply integral_congr_ae
  filter_upwards [] with z
  let x := projection (φ z)
  have hx := sourcePoint_coordinates r q z
  have hc := sourcePoint_in_chart r q z
  by_cases hz : z ∈ U
  · have hxK : x ∈ K := hz
    have hBase : z.1.val ∈ (chartAt E q.center) '' K := ⟨x, hxK, hx⟩
    obtain ⟨hφ, hFreq⟩ := receivingFourier_mode_eq_roundPhase r q d z (hSub hxK).2 m hDegree
    rw [indicator_of_mem hz, receivedOriginalJetDensity_eq_ordered_sum]
    simp only [T, Θ, φ, hφ, hFreq, chartInverseCutoffComplexSquare, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun l _ => ?_))
    have hi := inverseJetEntry_eq_tensorJetTransition c d hc i k
    have hj := inverseJetEntry_eq_tensorJetTransition c d hc j l
    change c.chart x = z.1 at hx
    rw [hx] at hi hj
    rw [← hi, ← hj, Complex.conj_ofReal]
    dsimp only [F, p, physicalCoefficient, movingChartAngularSymbol]
    rw [hα k _ hBase, hβ l _ hBase, hPull _ hBase]
    push_cast
    ring
  · rw [indicator_of_notMem hz]
    refine Finset.sum_eq_zero (fun k _ => Finset.sum_eq_zero (fun l _ => ?_))
    have hxOut : z.1.val ∉ (chartAt E q.center) '' K := by
      rintro ⟨y, hy, he⟩
      apply hz
      have hyS := (hSub hy).1.1
      change x ∈ K
      change (chartAt E q.center).symm z.1.val ∈ K
      rwa [← he, (chartAt E q.center).left_inv hyS]
    have hZero : (α k : E → ℝ) z.1.val = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxOut (hαS k h))
    simp only [F, physicalCoefficient, hZero, Complex.ofReal_zero, zero_mul]

end Burnett.Microlocal.Overlap
