import Burnett.Analysis.Microlocal.Overlap.LocalCutoffPairing
import Burnett.Analysis.Microlocal.PhysicalChartCover

/-! A smaller same-chart cutoff has a representation on the original subsequence. -/

set_option autoImplicit false
set_option maxRecDepth 2500
set_option maxHeartbeats 1400000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Geometry.FlatRigidity (exists_smooth_cutoff_on_compact_chart)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts
  (CompactChartInput RepresentsCompactJetPairings exists_countable_originalVolume_matrixDensities)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.SeparablePositive (finiteSeparableOperator separableOperator)
open Burnett.Microlocal.SmoothBaseTests (BallData)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open scoped BigOperators ComplexConjugate ContDiff InnerProduct Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

private theorem cutoffQuotient_smooth (η χ : D)
    (hNZ : ∀ x ∈ tsupport (η : E → ℝ), (χ : E → ℝ) x ≠ 0) :
    ContDiff ℝ ∞ (fun x : E => (η : E → ℝ) x * ((χ : E → ℝ) x)⁻¹) := by
  rw [← contDiffOn_univ]
  apply contDiffOn_of_locally_contDiffOn
  intro x _
  by_cases hx : (χ : E → ℝ) x = 0
  · have hx' : x ∉ tsupport (η : E → ℝ) := fun hh => hNZ x hh hx
    refine ⟨(tsupport (η : E → ℝ))ᶜ, isClosed_closure.isOpen_compl, hx', ?_⟩
    refine (contDiff_const (c := (0 : ℝ))).contDiffOn.congr ?_
    intro y hy
    rw [image_eq_zero_of_notMem_tsupport hy.2, zero_mul]
  · let U : Set E := (χ : E → ℝ) ⁻¹' ({0}ᶜ : Set ℝ)
    refine ⟨U, isClosed_singleton.isOpen_compl.preimage (test_smooth χ).continuous, hx, ?_⟩
    exact (test_smooth η).contDiffOn.mul ((test_smooth χ).contDiffOn.inv (fun _ h => h.2))

/-- The smooth quotient of two cutoffs when the denominator is nonzero on
the numerator's closed support. -/
def cutoffQuotient (η χ : D)
    (hNZ : ∀ x ∈ tsupport (η : E → ℝ), (χ : E → ℝ) x ≠ 0) : D :=
  ⟨fun x : E => (η : E → ℝ) x * ((χ : E → ℝ) x)⁻¹,
    ⟨cutoffQuotient_smooth η χ hNZ, (test_compactSupport η).mul_right⟩⟩

theorem cutoffQuotient_mul (η χ : D)
    (hNZ : ∀ x ∈ tsupport (η : E → ℝ), (χ : E → ℝ) x ≠ 0) (x : E) :
    (η : E → ℝ) x = (cutoffQuotient η χ hNZ : E → ℝ) x * (χ : E → ℝ) x := by
  change (η : E → ℝ) x = ((η : E → ℝ) x * ((χ : E → ℝ) x)⁻¹) * (χ : E → ℝ) x
  by_cases hx : x ∈ tsupport (η : E → ℝ)
  · rw [mul_assoc, inv_mul_cancel₀ (hNZ x hx), mul_one]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]

/-- Localizing the original geometric half-density by another smooth real
cutoff admits a positive representation on the already represented subsequence. -/
theorem originalVolume_represents_cutoffMul_on_sameSubsequence
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q : CompactChartInput M) (L : BallData)
    (hL : L.closedBall ⊆ (chartAt CoordinateSpace q.center).target)
    (χ' θ : D) (hχ' : tsupport (χ' : E → ℝ) ⊆ L.closedBall)
    (hCut : ∀ x : E, (χ' : E → ℝ) x = (θ : E → ℝ) x * (q.cutoff : E → ℝ) x)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf) :
    ∃ ν' : (JetSlot → ℂ) → Measure (Chart L), ∃ hfin : ∀ v, IsFiniteMeasure (ν' v),
      RepresentsCompactJetPairings L
        (originalGradient_volumeWeightedL2 B g hB hg hn q.center χ' (hχ'.trans hL)) σ ν' hfin := by
  let d : CompactChartInput M := ⟨q.center, L, hL, χ', hχ'⟩
  let w := originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
    (q.cutoff_support.trans q.ball_in_chart)
  let w' := originalGradient_volumeWeightedL2 B g hB hg hn q.center χ' (hχ'.trans hL)
  let a := physicalCoefficient θ
  have hSmooth : ContDiff ℝ ∞ (a : E → ℂ) := Complex.ofRealCLM.contDiff.comp (test_smooth θ)
  have hSupp : HasCompactSupport (a : E → ℂ) := (test_compactSupport θ).comp_left Complex.ofReal_zero
  have hInput (n : ℕ) (k : JetSlot) : w' n k = symbolCLM a (w n k) :=
    originalGradient_volumeWeightedL2_of_cutoff_mul B g hB hg hn q.center q.cutoff χ' θ
      (q.cutoff_support.trans q.ball_in_chart) (hχ'.trans hL) hCut n k
  obtain ⟨f, C, hC, hF, hS, hBound, hWeak⟩ :=
    exists_originalVolume_weakL2_representatives r B g hB hg hn hconv hb q
  have hN (n : ℕ) (j : JetSlot) : ‖w n j‖ ≤ C := by
    simpa only [hF n j, w] using hBound n j
  have hw (j : JetSlot) (v : ComplexL2 E) :
      Tendsto (fun n => inner ℂ v (w n j)) atTop (𝓝 0) := by
    simpa only [hF] using hWeak j v
  obtain ⟨t, ht, hReps⟩ := exists_countable_originalVolume_matrixDensities r B g hB hg hn
    hconv hb (fun _ : Unit => d) σ hσ
  obtain ⟨ν', hfin, hReg, hTrace, hPSD, hAC, hSet, hDensity, hLimit⟩ := hReps ()
  refine ⟨ν', hfin, hReg, hTrace, hPSD, hAC, hSet, hDensity, ?_⟩
  intro J _ b m hb' hm hd i j
  have hExists (l : J) : ∃ z : ℂ,
      Tendsto (fun n => inner ℂ (w' (σ n) i) (separableOperator (b l) (m l) (w' (σ n) j)))
        atTop (𝓝 z) := by
    refine ⟨∫ p : Chart q.ball, b l p.1 * conj (a p.1) * a p.1 * m l p.2 *
      density ν hf p i j ∂traceMeasure ν, ?_⟩
    have h := weightedTargetSlots_tendsto_density q.ball w σ hσ ν hf hRep f hF hS C hC hN hw
      (b l) (m l) (m l) (hb' l) (hm l) (hd l) 0 (fun _ _ => rfl)
      (fun _ : Unit => a) (fun _ : Unit => a)
      (fun _ => hSmooth.continuous) (fun _ => hSmooth) (fun _ => hSupp) (fun _ => i) (fun _ => j)
    simpa only [Fintype.sum_unique, hInput] using h
  choose z hz using hExists
  have hSum : Tendsto (fun n => inner ℂ (w' (σ n) i) (finiteSeparableOperator b m (w' (σ n) j)))
      atTop (𝓝 (∑ l, z l)) := by
    simpa only [finiteSeparableOperator, ContinuousLinearMap.sum_apply, inner_sum] using
      tendsto_finset_sum Finset.univ (fun l _ => hz l)
  have hSame := tendsto_nhds_unique (hSum.comp ht.tendsto_atTop) (hLimit J b m hb' hm hd i j)
  rw [← hSame]
  exact hSum

/-- Any smooth compact cutoff inside the original nonzero locus inherits a
representation on the same subsequence, including a cutoff with a plateau. -/
theorem originalVolume_represents_cutoffInside_nonzero_on_sameSubsequence
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q : CompactChartInput M) (L : BallData)
    (hL : L.closedBall ⊆ (chartAt CoordinateSpace q.center).target)
    (χ' : D) (hχ' : tsupport (χ' : E → ℝ) ⊆ L.closedBall)
    (hNZ : ∀ x ∈ tsupport (χ' : E → ℝ), (q.cutoff : E → ℝ) x ≠ 0)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf) :
    ∃ ν' : (JetSlot → ℂ) → Measure (Chart L), ∃ hfin : ∀ v, IsFiniteMeasure (ν' v),
      RepresentsCompactJetPairings L
        (originalGradient_volumeWeightedL2 B g hB hg hn q.center χ' (hχ'.trans hL)) σ ν' hfin :=
  originalVolume_represents_cutoffMul_on_sameSubsequence r B g hB hg hn hconv hb q L hL
    χ' (cutoffQuotient χ' q.cutoff hNZ) hχ' (cutoffQuotient_mul χ' q.cutoff hNZ) σ hσ ν hf hRep

/-- About any point of a represented nonzero locus, choose a smaller original
chart problem inside a prescribed open neighborhood, with a unit plateau and
the same represented subsequence. -/
theorem exists_originalVolume_sameChart_plateau_on_sameSubsequence
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q : CompactChartInput M) {x : M} (hx : x ∈ q.nonzeroLocus)
    {U : Set M} (hU : IsOpen U) (hxU : x ∈ U)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf) :
    let e := chartAt CoordinateSpace q.center
    ∃ (L : BallData) (δ : ℝ) (χ : D)
      (hL : L.closedBall ⊆ e.target) (hχ : tsupport (χ : E → ℝ) ⊆ L.closedBall),
      L.center = e x ∧ 0 < δ ∧ δ < L.radius ∧
      L.closedBall ⊆ e '' (U ∩ q.nonzeroLocus) ∧
      tsupport (χ : E → ℝ) ⊆ Metric.ball L.center L.radius ∧
      (∀ y, 0 ≤ (χ : E → ℝ) y ∧ (χ : E → ℝ) y ≤ 1) ∧
      (∀ y ∈ Metric.closedBall L.center δ, (χ : E → ℝ) y = 1) ∧
      ∃ ν' : (JetSlot → ℂ) → Measure (Chart L), ∃ hfin : ∀ v, IsFiniteMeasure (ν' v),
        RepresentsCompactJetPairings L
          (originalGradient_volumeWeightedL2 B g hB hg hn q.center χ (hχ.trans hL)) σ ν' hfin := by
  intro e
  let V := e '' (U ∩ q.nonzeroLocus)
  have hOpen : IsOpen V := e.isOpen_image_of_subset_source
    (hU.inter q.isOpen_nonzeroLocus) (fun _ hy => hy.2.1)
  have hxV : e x ∈ V := mem_image_of_mem e ⟨hxU, hx⟩
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp (hOpen.mem_nhds hxV)
  let R := ε / 2
  let δ := R / 2
  have hR : 0 < R := half_pos hε
  have hδ : 0 < δ := half_pos hR
  have hδR : δ < R := half_lt_self hR
  let L : BallData := ⟨e x, R, hR.le⟩
  have hLV : L.closedBall ⊆ V := (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεV
  have hL : L.closedBall ⊆ e.target := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hLV hy
    exact e.map_source hz.2.1
  obtain ⟨H, _, _, hH, f, hSmooth, hCompact, hSupport, hBound, hOne⟩ :=
    exists_smooth_cutoff_on_compact_chart
      (isCompact_closedBall (e x) δ) Metric.isOpen_ball (Metric.closedBall_subset_ball hδR)
  let χ : D := ⟨f, hSmooth, hCompact⟩
  have hSupp : tsupport (χ : E → ℝ) ⊆ Metric.ball L.center L.radius := hSupport.trans hH
  have hχ : tsupport (χ : E → ℝ) ⊆ L.closedBall := hSupp.trans Metric.ball_subset_closedBall
  have hNZ (y : E) (hy : y ∈ tsupport (χ : E → ℝ)) : (q.cutoff : E → ℝ) y ≠ 0 := by
    obtain ⟨z, hz, rfl⟩ := hLV (hχ hy)
    exact hz.2.2
  refine ⟨L, δ, χ, hL, hχ, rfl, hδ, hδR, hLV, hSupp, hBound, hOne, ?_⟩
  exact originalVolume_represents_cutoffInside_nonzero_on_sameSubsequence r B g hB hg hn hconv hb
    q L hL χ hχ hNZ σ hσ ν hf hRep

end Burnett.Microlocal.Overlap
