import Burnett.Geometry.Cotangent.CausalPulse.CanonicalOrbitPulse
import Burnett.Geometry.Cotangent.CausalPulse.CompactParameterIntegral

set_option autoImplicit false
set_option maxHeartbeats 5600000

noncomputable section

namespace Burnett.Geometry.CausalOrbitPulse

open Set Filter Bundle MeasureTheory
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.CotangentCauchyCrossing
open Burnett.Geometry.CotangentHamiltonInitialFamily
open Burnett.Geometry.UnitNullAngular (Phase)
open Burnett.GeometricAnalysis (contDiffOn_compact_parameter_integral)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M]

/-- Integrate a smooth base function over a fixed compact affine-time set
using the actual maximal punctured flow. -/
def fixedTimePulse (f : M → ℝ) (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (K : Set ℝ) (p : CotangentBundle M) : ℝ :=
  ∫ t in K, f ((maximalPuncturedFlow g hg hn hs (p, t)).1)

theorem contMDiffAt_fixedTimePulse (f : M → ℝ) (hf : ContMDiff Model 𝓘(ℝ) ∞ f)
    (g : Field (M := M)) (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (K : Set ℝ) (hK : IsCompact K) (p : CotangentBundle M)
    (hDom : ∀ t ∈ K, (p, t) ∈ maximalPuncturedFlowDomain g hg hn hs) :
    ContMDiffAt CotangentModelWithCorners 𝓘(ℝ) ∞ (fixedTimePulse f g hg hn hs K) p := by
  let F := maximalPuncturedFlow g hg hn hs
  let D := maximalPuncturedFlowDomain g hg hn hs
  have hFS := maximalPuncturedFlow_jointSmooth g hg hn hs
  let c := p.1
  have hP : p ∈ cotangentSource c := mem_chart_source CoordinateSpace c
  let q := cotangentChart c p
  have hQ : q ∈ phaseTarget c := cotangentChart_mapsTo c hP
  let L (z : Phase × ℝ) : CotangentBundle M × ℝ := (cotangentChartInverse c z.1, z.2)
  let O : Set (Phase × ℝ) := phaseTarget c ×ˢ (univ : Set ℝ)
  let S := O ∩ L ⁻¹' D
  have hO : IsOpen O := (isOpen_phaseTarget c).prod isOpen_univ
  have hL : ContMDiffOn (CoordinatePhaseModel.prod 𝓘(ℝ)) (CotangentModelWithCorners.prod 𝓘(ℝ)) ∞ L O :=
    ((contMDiffOn_cotangentChartInverse c).comp contMDiff_fst.contMDiffOn (fun _ h => h.1)).prodMk
      contMDiff_snd.contMDiffOn
  have hS : IsOpen S := hL.continuousOn.isOpen_inter_preimage hO hFS.1
  have hQS (t : ℝ) (ht : t ∈ K) : (q, t) ∈ S := by
    refine ⟨⟨hQ, trivial⟩, ?_⟩
    change (cotangentChartInverse c q, t) ∈ D
    rw [cotangentChart_left_inv c hP]
    exact hDom t ht
  have hTube : Prod.swap ⁻¹' S ∈ 𝓝ˢ K ×ˢ 𝓝 q := by
    apply hK.mem_nhdsSet_prod_of_forall
    intro t ht
    rw [← nhds_prod_eq]
    exact (hS.preimage continuous_swap).mem_nhds (hQS t ht)
  obtain ⟨V, hV, U, hU, hVU⟩ := mem_prod_iff.mp hTube
  obtain ⟨V', hV', hKV', hV'V⟩ := mem_nhdsSet_iff_exists.mp hV
  obtain ⟨U', hU'U, hU', hqU'⟩ := mem_nhds_iff.mp hU
  have hUS : U' ×ˢ V' ⊆ S := fun z hz => hVU (show z.swap ∈ V ×ˢ U from ⟨hV'V hz.2, hU'U hz.1⟩)
  have hProj : ContMDiff CotangentModelWithCorners Model ∞ (fun z : CotangentBundle M => z.1) :=
    contMDiff_proj (𝕜 := ℝ) (IB := Model) (n := ∞) (CotangentFiber (M := M))
  let G (z : Phase × ℝ) : ℝ := f ((F (L z)).1)
  have hG : ContMDiffOn (CoordinatePhaseModel.prod 𝓘(ℝ)) 𝓘(ℝ) ∞ G S :=
    (hf.comp hProj).comp_contMDiffOn (hFS.2.comp (hL.mono inter_subset_left) (fun _ h => h.2))
  have hGD : ContDiffOn ℝ ∞ G (U' ×ˢ V') := by
    have hSelf : ContMDiffOn 𝓘(ℝ, Phase × ℝ) 𝓘(ℝ) ∞ G (U' ×ˢ V') := by
      simpa only [CoordinatePhaseModel, Model, ← modelWithCornersSelf_prod, chartedSpaceSelf_prod,
        ModelProd] using hG.mono hUS
    exact hSelf.contDiffOn
  have hIn := (contDiffOn_compact_parameter_integral hU' hV' hK hKV' hGD).contDiffAt (hU'.mem_nhds hqU')
  let J : Phase → ℝ := fun u => ∫ t in K, G (u, t)
  have hI : ContMDiffAt CoordinatePhaseModel 𝓘(ℝ) ∞ J q := by
    simpa only [CoordinatePhaseModel, Model, ← modelWithCornersSelf_prod, chartedSpaceSelf_prod] using hIn.contMDiffAt
  have hCompose := hI.comp p ((contMDiffOn_cotangentChart c).contMDiffAt ((isOpen_cotangentSource c).mem_nhds hP))
  have hEq : fixedTimePulse f g hg hn hs K =ᶠ[𝓝 p] J ∘ cotangentChart c := by
    filter_upwards [(isOpen_cotangentSource c).mem_nhds hP] with x hx
    change (∫ t in K, f ((F (x, t)).1)) = ∫ t in K, f ((F (cotangentChartInverse c (cotangentChart c x), t)).1)
    rw [cotangentChart_left_inv c hx]
  exact hCompose.congr_of_eventuallyEq hEq

end Burnett.Geometry.CausalOrbitPulse
