import Burnett.Analysis.FrozenTransport.PatchCorrection.CommonFarGaugeProfileJets
import Burnett.Analysis.FrozenTransport.PatchCorrection.LocalFrequencyTest
import Burnett.Analysis.TransportPatches.WideJointWindow

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option maxRecDepth 4500

noncomputable section

namespace Burnett.V11

open Set Matrix Burnett.C02 Burnett.V03 Burnett.V06 Burnett.V08 Burnett.RicciSymbol Burnett.Geometry
open Burnett.V10.OriginalGaugeCompatibility
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.TransportWardSymbol (Mat inverseMatrix metricDensity)
open Burnett.Analysis.ProjectiveNullCaps (thinConeProfile scaledConeRatio quadratic descendingProfile_contDiff)
open Burnett.RicciSymbol.TensorFrame (LorentzFrame)
open scoped ContDiff Manifold Matrix.Norms.Elementwise
open private orderedBasis from Burnett.Analysis.TransportPatches.ActualWideOrderedSymbols
open private chartInverseMetric_has_frame from Burnett.Analysis.TransportPatches.ActualWideScreenLipschitz

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M] [SecondCountableTopology M]

/-- The receiving chart supplies the compact Lorentz family on which the
one far guard is selected, including an empty window. -/
theorem compact_chartInverseMetric_family (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ c.chart.target) :
    IsCompact ((chartInverseMetric B c) '' K) ∧
      ∀ m ∈ (chartInverseMetric B c) '' K, Nonempty (LorentzFrame m) := by
  refine ⟨hK.image_of_continuousOn ((chartInverseMetric_smooth B hB hSig.isNondegenerate c).continuousOn.mono hKU), ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact chartInverseMetric_has_frame B hSig c (hKU hx)

/-- The very wide-screen witness used by the receiving C02 window supplies
both actual correction profiles with no second choice of cutoffs. -/
theorem exists_intrinsicCorrection_jets_of_jointWideScreen (B : Field (M := M)) (hB : IsSmooth B)
    (hSig : HasLorentzSignature B) (c : AtlasChart M) (V K : Set E)
    (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V) (hVU : V ⊆ c.chart.target)
    (i o : ℝ) (wide : HasJointWideScreen B c i o V)
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a (V ×ˢ {v : E | v ≠ 0}))
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (κ : ℝ) (hκ : 0 < κ) (δ b : ℝ)
    {η : ℝ} (hη : 0 < η) (inn out : ℝ) :
    let g := metricComponents (fixedForm B c)
    let m := chartInverseMetric B c
    let hm (x : E) (hx : x ∈ K) := wideScreen_frequencySmooth_of_joint wide (hKV hx)
    ∃ S : E → GaugeScreen, (∀ x (hx : x ∈ K), S x = (thinScreenAngular (m x) i o (hm x hx) hη inn out).matrix) ∧
      ∀ N : ℕ, ∃ Cjet : ℝ, 0 ≤ Cjet ∧ ∀ x (hx : x ∈ K), ∀ k j l,
        GaugeProfileBound N Cjet (gaugeTriadAngularProfile ϑ κ (m x) (metricDensity (g x))
          (fun ξ => a (x, ξ)) (gaugeFrozenContraction (m x)) (S x) k l j) ∧
        GaugeProfileBound N Cjet (actualFarAngularProfile (g x) (fun ξ => a (x, ξ)) ϑ κ δ b i o
          (hm x hx) hη inn out k j l) := by
  intro g m hm
  let S (x : E) : GaugeScreen := fun ξ k j =>
    thinConeProfile (m x) η inn out ξ * globalAngularScreenSymbol i o (m x) (orderedBasis j) (fun s => ξ s) k.1 k.2
  have same (x : E) (hx : x ∈ K) : S x = (thinScreenAngular (m x) i o (hm x hx) hη inn out).matrix := rfl
  have hmd : ContDiffOn ℝ ∞ m V := (chartInverseMetric_smooth B hB hSig.isNondegenerate c).mono hVU
  have hme (i j : Fin 4) : ContDiffOn ℝ ∞ (fun x => m x i j) V := contDiffOn_pi.mp (contDiffOn_pi.mp hmd i) j
  have hgd : ContDiffOn ℝ ∞ g V := contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j =>
    (fixedForm_components_smooth B hB c i j).mono hVU
  have hnd (x : E) (hx : x ∈ V) : g x ∈ nonsingularMetricDomain :=
    fixedForm_det_ne_zero B hSig.isNondegenerate c (hVU hx)
  let O := V ×ˢ {v : E | v ≠ 0}
  have hme' (i j : Fin 4) : ContDiffOn ℝ ∞ (fun x : Joint => m x.1 i j) O :=
    (hme i j).comp contDiff_fst.contDiffOn (fun _ h => h.1)
  have coord (i : Fin 4) : ContDiff ℝ ∞ (fun x : Joint => x.2 i) :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp contDiff_snd
  have q : ContDiffOn ℝ ∞ (fun x : Joint => quadratic (m x.1) x.2) O := by
    unfold quadratic Burnett.Analysis.ProjectiveNullCaps.pairing Burnett.Analysis.ProjectiveNullCaps.rowValue
    exact ContDiffOn.sum fun j _ => (ContDiffOn.sum fun k _ => (hme' k j).mul (coord k).contDiffOn).mul
      (coord j).contDiffOn
  have ratio : ContDiffOn ℝ ∞ (fun x : Joint => scaledConeRatio (m x.1) η x.2) O :=
    q.div (contDiff_const.mul (contDiff_snd.norm_sq ℝ)).contDiffOn fun _ hx =>
      mul_ne_zero hη.ne' (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx.2))
  have Sdiff (k j : TensorSlot) : ContDiffOn ℝ ∞ (fun x : Joint => S x.1 x.2 k j) O :=
    ((descendingProfile_contDiff _ _).comp_contDiffOn (ratio.pow 2)).mul (wide (orderedBasis j) k.1 k.2)
  obtain ⟨aGlobal, hGlobal, matchFiber⟩ := exists_local_frequency_test_extension V K hV hK hKV a ha
  refine ⟨S, same, ?_⟩
  intro N
  obtain ⟨Cjet, hCjet, jets⟩ := exists_commonFarGauge_profile_jets V K hV hK hKV g hgd hnd hme S Sdiff aGlobal hGlobal
    ϑ hϑ κ hκ δ b i o hm hη inn out same N
  refine ⟨Cjet, hCjet, ?_⟩
  intro x hx k j l
  have sameTest : (fun ξ => aGlobal (x, ξ)) = fun ξ => a (x, ξ) := funext (matchFiber x hx)
  simpa only [sameTest] using jets x hx k j l

end Burnett.V11
