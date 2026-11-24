import Burnett.Analysis.Microlocal.Overlap.ReceivingPlateauBaseWindow
import Burnett.Analysis.Microlocal.Overlap.ReceivingSquareWindowAssembly
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartWeakInputs
import Burnett.Analysis.Microlocal.Overlap.AtlasAngularPhaseEncoding
import Burnett.Analysis.Microlocal.Overlap.AngularLocalClassical

/-! Assemble the actual bounded receiving-chart operator across represented plateaus. -/

set_option autoImplicit false
set_option maxRecDepth 3300
set_option maxHeartbeats 3000000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open UnitCosphere (Cosphere projection)
open FixedCotangentChart (fixedChartPhase_of_mem)
open Burnett.Microlocal.AtlasVolumeGradient
open Burnett.Microlocal.BesselLocalization (physicalCoefficient coeffMul)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped Manifold Topology ContDiff BigOperators InnerProduct

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The right-linear ordered classical test in actual receiving coordinates. -/
def receivingClassicalTest {r : Metric (M := M)} (c : AtlasChart M)
    (A : IntrinsicAmplitudeCovariance r) (a : E → E → ℂ)
    (η₀ η₁ : D) (i j : JetSlot) (p : Cosphere r) : ℂ :=
  let z := atlasAngularPhaseCode c p
  ((physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) * a z.1 z.2.val) *
    atlasOrderedJetEntry c A.density p i j

private theorem atlasAngularPhaseCode_fst {r : Metric (M := M)} (c : AtlasChart M) (p : Cosphere r)
    (hp : projection p ∈ c.chart.source) :
    (atlasAngularPhaseCode c p).1 = c.chart (projection p) := by
  change (FixedCotangentChart.fixedChartPhase c p.val).1 = _
  rw [fixedChartPhase_of_mem c p.val hp]
  rfl

variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- The same actual bounded operator and original sequence pairings on
represented compact plateaus give the receiving-chart limit on the whole
compact test window. The integral uses one fixed intrinsic covariance. -/
theorem tendsto_receivingClassicalPairing_of_originalPlateauLimits
    {I : Type*} (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (q : I → CompactChartInput M)
    (ν : ∀ i, (JetSlot → ℂ) → Measure (Chart (q i).ball))
    (hf : ∀ i v, IsFiniteMeasure (ν i v))
    (hRep : ∀ i, let a := q i
      RepresentsCompactJetPairings a.ball
        (originalGradient_volumeWeightedL2 B g hB hg hn a.center a.cutoff
          (a.cutoff_support.trans a.ball_in_chart)) σ (ν i) (hf i))
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (hCover : K ⊆ ⋃ i, (q i).nonzeroLocus)
    (A : IntrinsicAmplitudeCovariance r) (a : E → E → ℂ) (S : Set E) (hS : IsCompact S)
    (hAS : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S)
    (hJoint : ContDiffOn ℝ ∞ (Function.uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (hZero : ContDiff ℝ ∞ (fun x => a x 0))
    (hDegree : ∀ x, Burnett.Microlocal.AngularCommutator.DegreeZero (a x))
    (η₀ η₁ : D) (h₀ : tsupport (η₀ : E → ℝ) ⊆ c.chart '' K)
    (h₁ : tsupport (η₁ : E → ℝ) ⊆ c.chart '' K)
    (T : ComplexL2 E →L[ℂ] ComplexL2 E)
    (hT : HasLocalClassicalRepresentation T a (tsupport (η₁ : E → ℝ)))
    (i j : JetSlot)
    (hLocal : ∀ (d : CompactChartInput M)
      (ρ : (JetSlot → ℂ) → Measure (Chart d.ball)) (hρ : ∀ v, IsFiniteMeasure (ρ v)),
      RepresentsCompactJetPairings d.ball
        (originalGradient_volumeWeightedL2 B g hB hg hn d.center d.cutoff
          (d.cutoff_support.trans d.ball_in_chart)) σ ρ hρ →
      d.ball.closedBall ⊆ ((AtlasChart.atPoint d.center).transition c).source →
      ∀ (L : Set M), IsCompact L → L ⊆ d.nonzeroLocus ∩ c.chart.source →
      ∀ (χ₀ χ₁ : D), tsupport (χ₀ : E → ℝ) ⊆ c.chart '' L →
      tsupport (χ₁ : E → ℝ) ⊆ c.chart '' L →
      ∀ (hχ₀ : tsupport (χ₀ : E → ℝ) ⊆ c.chart.target)
        (hχ₁ : tsupport (χ₁ : E → ℝ) ⊆ c.chart.target),
      HasLocalClassicalRepresentation T a (tsupport (χ₁ : E → ℝ)) →
      let G := receivingClassicalTest c A a χ₀ χ₁ i j
      let u := fixedVolumeGradientSchwartz B g hB hg hn c χ₀ hχ₀
      let v := fixedVolumeGradientSchwartz B g hB hg hn c χ₁ hχ₁
      IntegrableOn G (amplitudeCosphereWindow r L) A.control ∧
        Tendsto (fun n => inner ℂ ((u (σ n) i).toLp 2 volume) (T ((v (σ n) j).toLp 2 volume)))
          atTop (𝓝 (∫ p in amplitudeCosphereWindow r L, G p ∂A.control))) :
    let h₀c := h₀.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let h₁c := h₁.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let u := fixedVolumeGradientSchwartz B g hB hg hn c η₀ h₀c
    let v := fixedVolumeGradientSchwartz B g hB hg hn c η₁ h₁c
    let G := receivingClassicalTest c A a η₀ η₁ i j
    IntegrableOn G (amplitudeCosphereWindow r K) A.control ∧
      Tendsto (fun n => inner ℂ ((u (σ n) i).toLp 2 volume) (T ((v (σ n) j).toLp 2 volume)))
        atTop (𝓝 (∫ p in amplitudeCosphereWindow r K, G p ∂A.control)) := by
  classical
  intro h₀c h₁c u v G
  let L := c.chart '' K
  have hL : IsCompact L := hK.image_of_continuousOn (c.chart.continuousOn.mono hKc)
  have hLc : L ⊆ c.chart.target := image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc)
  have hLK : c.chart.symm '' L ⊆ K := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rwa [c.chart.left_inv (hKc hx)]
  obtain ⟨N, d, δ, χ, ρ, hρ, hSum, hData⟩ :=
    exists_receiving_square_partition_on_sameSubsequence r B g hB hg hn hconv hb σ hσ
      q ν hf hRep c L hL hLc (hLK.trans hCover)
  let K' (k : Fin N) := (chartAt E (d k).center).symm '' Metric.closedBall (d k).ball.center (δ k)
  have hBase (k : Fin N) := represented_closedPlateau_baseWindow (d k) c (δ k)
    (hData k).2.1.le (hData k).2.2.1 (hData k).2.2.2.2.1
  let χ₀ (k : Fin N) : D := ⟨fun x : E => (χ k : E → ℝ) x * (η₀ : E → ℝ) x,
    (test_smooth (χ k)).mul (test_smooth η₀), (test_compactSupport (χ k)).mul_right⟩
  let χ₁ (k : Fin N) : D := ⟨fun x : E => (χ k : E → ℝ) x * (η₁ : E → ℝ) x,
    (test_smooth (χ k)).mul (test_smooth η₁), (test_compactSupport (χ k)).mul_right⟩
  have hχ (k : Fin N) : tsupport (χ k : E → ℝ) ⊆ c.chart '' K' k :=
    (hBase k).2.2.symm ▸ (hData k).2.2.2.1
  have hχ₀ (k : Fin N) : tsupport (χ₀ k : E → ℝ) ⊆ c.chart '' K' k :=
    tsupport_mul_subset_left.trans (hχ k)
  have hχ₁ (k : Fin N) : tsupport (χ₁ k : E → ℝ) ⊆ c.chart '' K' k :=
    tsupport_mul_subset_left.trans (hχ k)
  have hχ₀c (k : Fin N) : tsupport (χ₀ k : E → ℝ) ⊆ c.chart.target :=
    tsupport_mul_subset_right.trans h₀c
  have hχ₁c (k : Fin N) : tsupport (χ₁ k : E → ℝ) ⊆ c.chart.target :=
    tsupport_mul_subset_right.trans h₁c
  have hT' (k : Fin N) : HasLocalClassicalRepresentation T a (tsupport (χ₁ k : E → ℝ)) := by
    obtain ⟨R, hR, hAction⟩ := hT
    exact ⟨R, hR, fun f w hw => hAction f w (hw.trans tsupport_mul_subset_right)⟩
  let p₀ (k : Fin N) := fixedVolumeGradientSchwartz B g hB hg hn c (χ₀ k) (hχ₀c k)
  let p₁ (k : Fin N) := fixedVolumeGradientSchwartz B g hB hg hn c (χ₁ k) (hχ₁c k)
  let Q (n : ℕ) := inner ℂ ((u (σ n) i).toLp 2 volume) (T ((v (σ n) j).toLp 2 volume))
  let Qloc (k : Fin N) (n : ℕ) := inner ℂ ((p₀ k (σ n) i).toLp 2 volume) (T ((p₁ k (σ n) j).toLp 2 volume))
  obtain ⟨B₀, hB₀, hBound₀, _⟩ := fixedVolumeGradient_weak_and_uniform_L2 r B g hB hg hn hconv hb c η₀ h₀c
  obtain ⟨B₁, _, hBound₁, hWeak⟩ := fixedVolumeGradient_weak_and_uniform_L2 r B g hB hg hn hconv hb c η₁ h₁c
  have hU (n : ℕ) : tsupport (u (σ n) i : E → ℂ) ⊆ L :=
    (fixedVolumeGradientSchwartz_tsupport B g hB hg hn c η₀ h₀c (σ n) i).trans h₀
  have hV (n : ℕ) : tsupport (v (σ n) j : E → ℂ) ⊆ tsupport (η₁ : E → ℝ) :=
    fixedVolumeGradientSchwartz_tsupport B g hB hg hn c η₁ h₁c (σ n) j
  have hErr := tendsto_classicalPairing_sub_squareCutoffSum χ L hL hSum a S hS hAS hJoint hZero hDegree
    T (tsupport (η₁ : E → ℝ)) hT (fun n => u (σ n) i) (fun n => v (σ n) j)
    hU (fun n => (hV n).trans h₁) hV B₀ B₁ hB₀ (fun n => hBound₀ (σ n) i)
    (fun n => hBound₁ (σ n) j) (fun w => (hWeak j w).comp hσ.tendsto_atTop)
  have hSplit : Tendsto (fun n => Q n - ∑ k, Qloc k n) atTop (𝓝 0) := by
    apply hErr.congr
    intro n
    dsimp only [Q, Qloc, u, v, p₀, p₁]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [coeffMul_fixedVolumeGradientSchwartz, coeffMul_fixedVolumeGradientSchwartz]
  let W := amplitudeCosphereWindow r K
  let W' (k : Fin N) := amplitudeCosphereWindow r (K' k)
  let π (p : Cosphere r) := (atlasAngularPhaseCode c p).1
  let F (p : Cosphere r) := if projection p ∈ c.chart.source then G p else 0
  have hOff (p : Cosphere r) (hp : p ∉ W) : F p = 0 := by
    change (if projection p ∈ c.chart.source then G p else 0) = 0
    by_cases hc : projection p ∈ c.chart.source
    · rw [if_pos hc]
      have hx : π p ∉ L := by
        rintro ⟨x, hx, he⟩
        have he' : c.chart x = c.chart (projection p) := he.trans (atlasAngularPhaseCode_fst c p hc)
        have hBaseMem : projection p ∈ K := c.chart.injOn (hKc hx) hc he' ▸ hx
        exact hp hBaseMem
      have hη : (η₀ : E → ℝ) (π p) = 0 := image_eq_zero_of_notMem_tsupport (fun hz => hx (h₀ hz))
      simp only [G, receivingClassicalTest, physicalCoefficient, show (atlasAngularPhaseCode c p).1 = π p from rfl,
        hη, Complex.ofReal_zero, zero_mul]
    · exact if_neg hc
  have hOne (p : Cosphere r) (hp : F p ≠ 0) : ∑ k, (χ k : E → ℝ) (π p) ^ 2 = 1 := by
    have hp' : p ∈ W := by
      by_contra hn
      exact hp (hOff p hn)
    rw [show π p = c.chart (projection p) from atlasAngularPhaseCode_fst c p (hKc hp')]
    exact hSum _ (mem_image_of_mem _ hp')
  have hOnly (k : Fin N) (p : Cosphere r) (hp : p ∉ W' k) : ((χ k : E → ℝ) (π p) ^ 2 : ℝ) * F p = 0 := by
    by_cases hc : projection p ∈ c.chart.source
    · have hz : (χ k : E → ℝ) (π p) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro h
        obtain ⟨x, hx, he⟩ := hχ k h
        have he' : c.chart x = c.chart (projection p) := he.trans (atlasAngularPhaseCode_fst c p hc)
        have hBaseMem : projection p ∈ K' k := c.chart.injOn ((hBase k).2.1 hx).2 hc he' ▸ hx
        exact hp hBaseMem
      simp only [hz, zero_pow (by decide : 2 ≠ 0), Complex.ofReal_zero, zero_mul]
    · simp only [F, if_neg hc, mul_zero]
  have hLocalL (k : Fin N) := hLocal (d k) (ρ k) (hρ k) (hData k).2.2.2.2.2
    (hData k).2.2.1 (K' k) (hBase k).1 (hBase k).2.1
    (χ₀ k) (χ₁ k) (hχ₀ k) (hχ₁ k) (hχ₀c k) (hχ₁c k) (hT' k)
  have hCompare (k : Fin N) : receivingClassicalTest c A a (χ₀ k) (χ₁ k) i j =ᵐ[A.control.restrict (W' k)]
      (fun p => ((χ k : E → ℝ) (π p) ^ 2 : ℝ) * F p) := by
    have hMeas : MeasurableSet (W' k) :=
      measurableSet_amplitudeCosphereWindow _ (hBase k).1.isClosed.measurableSet
    filter_upwards [ae_restrict_mem (μ := A.control) hMeas] with p hp
    have hpc : projection p ∈ c.chart.source := ((hBase k).2.1 hp).2
    simp only [receivingClassicalTest, physicalCoefficient, χ₀, χ₁, π, F, G, if_pos hpc,
      Complex.ofReal_mul, Complex.ofReal_pow]
    ring
  obtain ⟨hIF, hLimF⟩ := tendsto_classicalPairing_of_squareCutoff_windows A.control π χ W' F hOne hOnly
    (fun k => (hLocalL k).1.congr (hCompare k)) Q Qloc hSplit (fun k => by
      rw [← integral_congr_ae (hCompare k)]
      exact (hLocalL k).2)
  have hEq : F =ᵐ[A.control.restrict W] G := by
    have hMeas : MeasurableSet W := measurableSet_amplitudeCosphereWindow _ hK.isClosed.measurableSet
    filter_upwards [ae_restrict_mem (μ := A.control) hMeas] with p hp
    exact if_pos (hKc hp)
  refine ⟨hIF.integrableOn.congr hEq, ?_⟩
  change Tendsto Q atTop (𝓝 (∫ p in W, G p ∂A.control))
  rw [← integral_congr_ae hEq, setIntegral_eq_integral_of_forall_compl_eq_zero hOff]
  exact hLimF

end Burnett.Microlocal.Overlap
