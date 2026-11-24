import Burnett.Analysis.Microlocal.Overlap.ReceivingClassicalCoverAssembly
import Burnett.Analysis.Microlocal.Overlap.ReceivingChartOriginalClassicalWindow
import Burnett.Analysis.Microlocal.Overlap.ReceivingPaperConvention
import Burnett.Analysis.Microlocal.Overlap.OriginalVacuumIntrinsicAmplitude

/-! The actual original classical pairings in every compatible fixed chart. -/

set_option autoImplicit false
set_option maxRecDepth 3300
set_option maxHeartbeats 3000000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Set Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldMetricSequence ManifoldBilinear MaximalChart
open UnitCosphere (Cosphere projection)
open FixedCotangentChart (fixedChartPhase fixedChartPhase_of_mem)
open Burnett.Microlocal.AtlasVolumeGradient (fixedVolumeGradientSchwartz)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.X02.SobolevTestJet (D)
open scoped ComplexConjugate ContDiff Manifold Topology InnerProduct

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The represented cover can be used uniformly, including on an empty base. -/
private theorem exists_originalRepresented_family
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hn : IsNondegenerate B) (σ : ℕ → ℕ) (h : HasOriginalRepresentedCover B g hB hg hn σ) :
    ∃ (I : Type) (q : I → CompactChartInput M)
      (ν : ∀ i, (JetSlot → ℂ) → Measure (Chart (q i).ball)) (hf : ∀ i v, IsFiniteMeasure (ν i v)),
      (⋃ i, (q i).nonzeroLocus) = univ ∧
      ∀ i, let a := q i
        RepresentsCompactJetPairings a.ball
          (originalGradient_volumeWeightedL2 B g hB hg hn a.center a.cutoff
            (a.cutoff_support.trans a.ball_in_chart)) σ (ν i) (hf i) := by
  by_cases hm : Nonempty M
  · obtain ⟨q, hCover, ν, hf, hRep⟩ := h hm
    refine ⟨ℕ, q, ν, hf, ?_, fun i => (hRep i).1⟩
    apply eq_univ_of_forall
    intro x
    have hx : x ∈ ⋃ i, (q i).cutoffLocusAbove (1 / 2) := hCover.symm ▸ mem_univ x
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, (q i).cutoffLocusAbove_subset_nonzeroLocus (by norm_num) hi⟩
  · refine ⟨Fin 0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, ?_, fun i => i.elim0⟩
    exact eq_univ_of_forall fun x => (hm ⟨x⟩).elim

variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] [T2Space M]

/-- The whole receiving-window test is obtained on the already constructed
global amplitude and original subsequence. The only operator premise is its
actual local classical representation. -/
theorem tendsto_originalVolume_receivingClassicalPairing_globalAmplitude
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A)
    (c : AtlasChart M) (K : Set M) (hK : IsCompact K) (hKc : K ⊆ c.chart.source)
    (a : E → E → ℂ) (S : Set E) (hS : IsCompact S)
    (hAS : ∀ ξ, tsupport (fun x => a x ξ) ⊆ S)
    (hJoint : ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)))
    (hZero : ContDiff ℝ ∞ (fun x => a x 0)) (hDegree : ∀ x, DegreeZero (a x))
    (η₀ η₁ : D) (h₀ : tsupport (η₀ : E → ℝ) ⊆ c.chart '' K)
    (h₁ : tsupport (η₁ : E → ℝ) ⊆ c.chart '' K)
    (T : ComplexL2 E →L[ℂ] ComplexL2 E)
    (hT : HasLocalClassicalRepresentation T a (tsupport (η₁ : E → ℝ))) (i j : JetSlot) :
    let h₀c := h₀.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let h₁c := h₁.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
    let u := fixedVolumeGradientSchwartz B g hB hg hnB c η₀ h₀c
    let v := fixedVolumeGradientSchwartz B g hB hg hnB c η₁ h₁c
    let G := receivingClassicalTest c A a η₀ η₁ i j
    IntegrableOn G (amplitudeCosphereWindow r K) A.control ∧
      Tendsto (fun n => inner ℂ ((u (σ n) i).toLp 2 volume) (T ((v (σ n) j).toLp 2 volume)))
        atTop (𝓝 (∫ p in amplitudeCosphereWindow r K, G p ∂A.control)) := by
  obtain ⟨hCover, _, _, _, hLaws, _⟩ := hA
  obtain ⟨I, q, ν, hf, hWhole, hRep⟩ := exists_originalRepresented_family B g hB hg hnB σ hCover
  have hKCov : K ⊆ ⋃ i, (q i).nonzeroLocus := by rw [hWhole]; exact subset_univ K
  refine tendsto_receivingClassicalPairing_of_originalPlateauLimits r B g hB hg hnB hconv hb σ hσ
    q ν hf hRep c K hK hKc hKCov A a S hS hAS hJoint hZero hDegree η₀ η₁ h₀ h₁ T hT i j ?_
  intro d ρ hρ hRep' hOuter L hL hSub χ₀ χ₁ hχ₀ hχ₁ hχ₀c hχ₁c hT'
  exact tendsto_originalVolume_receivingClassicalPairing_on_compact r B g hB hg hsB hsG hnB hnG
    hconv hb hv σ hσ A hLaws d ρ hρ hRep' c hL hSub hOuter a S hS hAS hJoint hZero hDegree
    χ₀ χ₁ hχ₀ hχ₁ hχ₀c hχ₁c T hT' i j

/-- Equation eq:sigma in the manuscript convention for every fixed receiving
chart, with the symbol evaluated at the actual auxiliary unit covector. -/
def HasOriginalReceivingPaperPairings
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r) : Prop :=
  ∀ (c : AtlasChart M) (K : Set M), IsCompact K → ∀ (hKc : K ⊆ c.chart.source)
    (a : E → E → ℂ) (S : Set E), IsCompact S →
    (∀ ξ, tsupport (fun x => a x ξ) ⊆ S) →
    ContDiffOn ℝ ∞ (uncurry a) (univ ×ˢ ({0}ᶜ : Set E)) →
    ContDiff ℝ ∞ (fun x => a x 0) → (∀ x, DegreeZero (a x)) →
    ∀ (η₀ η₁ : D) (h₀ : tsupport (η₀ : E → ℝ) ⊆ c.chart '' K)
      (h₁ : tsupport (η₁ : E → ℝ) ⊆ c.chart '' K) (T : ComplexL2 E →L[ℂ] ComplexL2 E),
    HasLocalClassicalRepresentation T a (tsupport (η₁ : E → ℝ)) → ∀ i j : JetSlot,
      let h₀c := h₀.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
      let h₁c := h₁.trans (image_subset_iff.mpr (c.chart.mapsTo.mono_left hKc))
      let u := fixedVolumeGradientSchwartz B g hB hg hn c η₀ h₀c
      let v := fixedVolumeGradientSchwartz B g hB hg hn c η₁ h₁c
      let τ := A.control.restrict (amplitudeCosphereWindow r K)
      let G (p : Cosphere r) :=
        let z := fixedChartPhase c p.val
        conj ((physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) * a z.1 (WithLp.toLp 2 z.2)) *
          atlasOrderedJetEntry c A.density p j i
      Integrable G τ ∧
        Tendsto (fun n => inner ℂ (T ((v (σ n) j).toLp 2 volume)) ((u (σ n) i).toLp 2 volume))
          atTop (𝓝 (∫ p, G p ∂τ))

/-- Once the global original amplitude is constructed, every actual
represented receiving-chart test reads that same density along its sequence. -/
theorem hasOriginalReceivingPaperPairings_of_intrinsicAmplitude
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalIntrinsicAmplitude r B g hB hg hnB σ A) :
    HasOriginalReceivingPaperPairings r B g hB hg hnB σ A := by
  intro c K hK hKc a S hS hAS hJoint hZero hDegree η₀ η₁ h₀ h₁ T hT i j h₀c h₁c u v τ G
  obtain ⟨hI, hLim⟩ := tendsto_originalVolume_receivingClassicalPairing_globalAmplitude r B g hB hg hsB hsG
    hnB hnG hconv hb hv σ hσ A hA c K hK hKc a S hS hAS hJoint hZero hDegree η₀ η₁ h₀ h₁ T hT i j
  let w (p : Cosphere r) :=
    let z := fixedChartPhase c p.val
    (physicalCoefficient η₀ z.1 * physicalCoefficient η₁ z.1) * a z.1 (WithLp.toLp 2 z.2)
  let F (p : Cosphere r) := w p * atlasOrderedJetEntry c A.density p i j
  have hAE : receivingClassicalTest c A a η₀ η₁ i j =ᵐ[τ] F := by
    have hWin := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
    filter_upwards [ae_restrict_mem (μ := A.control) hWin] with p hp
    dsimp only [receivingClassicalTest, F, w]
    rw [atlasAngularPhaseCode_symbol_eq_unitCovector c p (hKc hp) a hDegree]
    exact congrArg
      (fun x => ((physicalCoefficient η₀ (fixedChartPhase c p.val).1 *
        physicalCoefficient η₁ (fixedChartPhase c p.val).1) * a x (WithLp.toLp 2 (atlasChartUnitCovector c p))) *
        atlasOrderedJetEntry c A.density p i j)
      ((congrArg Prod.fst (fixedChartPhase_of_mem c p.val (hKc hp))).symm)
  change Tendsto _ atTop (𝓝 (∫ p, receivingClassicalTest c A a η₀ η₁ i j p ∂τ)) at hLim
  rw [integral_congr_ae hAE] at hLim
  have hPos := hA.2.2.2.2.2.mono (fun p hp => hp.2.1)
  obtain ⟨hG, _, hLimG⟩ := tendsto_receivingPaperPairing_of_weight A c hPos hK.isClosed.measurableSet hKc
    w i j (fun n => (u (σ n) i).toLp 2 volume) (fun n => (v (σ n) j).toLp 2 volume) T
    (hI.congr hAE) hLim
  exact ⟨hG, hLimG⟩

end Burnett.Microlocal.Overlap
