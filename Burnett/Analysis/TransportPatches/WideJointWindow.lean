import Burnett.Analysis.TransportPatches.WideCompatibleWindow
import Mathlib.Topology.MetricSpace.Thickening

/-! Choose common wide cutoffs with an open base collar for frequency derivatives. -/
set_option autoImplicit false
set_option maxRecDepth 5200
set_option maxHeartbeats 6600000

noncomputable section

namespace Burnett.C02

open Set Matrix Burnett.RicciSymbol Burnett.V06 Burnett.Geometry TensorFrame
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.A02.FrequencySplit (E)
open Burnett.Geometry.UnitCosphere (Cosphere hamiltonian projection)
open Burnett.Microlocal.Overlap
open Burnett.P01 (principalGaugeProjection)
open scoped ContDiff Manifold

open private chartInverseMetric_isUnit chartInverseMetric_has_frame from Burnett.Analysis.TransportPatches.ActualWideScreenLipschitz

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

def HasJointWideScreen (B : Field (M := M)) (c : AtlasChart M)
    (i o : ℝ) (V : Set E) : Prop :=
  ∀ H : ScreenMatrix, ∀ a b : Index, ContDiffOn ℝ ∞ (fun p : E × E =>
    globalAngularScreenSymbol i o (chartInverseMetric B c p.1) H (fun j => p.2 j) a b)
    (V ×ˢ ({0}ᶜ : Set E))

private theorem contDiff_frequencySlice (f : E × E → ℝ) (V : Set E)
    (h : ContDiffOn ℝ ∞ f (V ×ˢ ({0}ᶜ : Set E))) (x : E) (hx : x ∈ V) :
    ContDiffOn ℝ ∞ (fun ξ : E => f (x, ξ)) ({0}ᶜ : Set E) := by
  let slice (ξ : E) : E × E := (x, ξ)
  have hSlice : ContDiff ℝ ∞ slice := contDiff_const.prodMk contDiff_id
  have hMap : MapsTo slice ({0}ᶜ : Set E) (V ×ˢ ({0}ᶜ : Set E)) := fun _ hξ => ⟨hx, hξ⟩
  exact h.comp hSlice.contDiffOn hMap

omit [IsManifold Model ∞ M] [SecondCountableTopology M] in
theorem wideScreen_frequencySmooth_of_joint {B : Field (M := M)} {c : AtlasChart M}
    {i o : ℝ} {V : Set E} (h : HasJointWideScreen B c i o V) {x : E} (hx : x ∈ V) :
    WideScreenFrequencySmooth i o (chartInverseMetric B c x) := by
  intro H a b
  let f (p : E × E) := globalAngularScreenSymbol i o (chartInverseMetric B c p.1) H (fun j => p.2 j) a b
  have hs : ContDiffOn ℝ ∞ f (V ×ˢ ({0}ᶜ : Set E)) := h H a b
  simpa only [f] using contDiff_frequencySlice f V hs x hx

def HasWideRicciRangeSlope (r : Metric (M := M)) (B : Field (M := M)) (hSig : HasLorentzSignature B)
    (c : AtlasChart M) (K : Set E) (i o L C η : ℝ) : Prop :=
  ∀ x₀ ∈ K, ∀ p : Cosphere r, projection p ∈ c.chart.source →
    c.chart (projection p) ∈ K → hamiltonian B hSig.isNondegenerate p = 0 →
    ∀ d : ℝ, ‖c.chart (projection p) - x₀‖ ≤ d → d ≤ 1 → L * d ≤ η →
    ∀ k : ComplexTensor2, IsSymmetricComplexTensor k →
      (∀ a b, complexRicciSymbol (chartInverseMetric B c (c.chart (projection p)))
        (atlasChartUnitCovector c p) k a b = 0) →
    let m := chartInverseMetric B c x₀
    let q := atlasChartUnitCovector c p
    let ξ : E := WithLp.toLp 2 q
    let J : ComplexTensor2 := principalGaugeProjection ξ k
    let S := complexWideScreen i o m J q
    ‖J - S‖ ≤ C * d * ‖J‖ ∧ ‖(normalizedFrozenPhase m ξ : ℂ) • S‖ ≤ C * d * ‖J‖

/-- The collar and the Ricci-range slope use one pair of actual wide cutoffs. -/
theorem exists_wideJointWindow {r : Metric (M := M)}
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target) :
    ∃ (i o L C η : ℝ) (V : Set E), 0 < i ∧ i < o ∧ 0 ≤ L ∧ 0 ≤ C ∧ 0 < η ∧
      IsOpen V ∧ K ⊆ V ∧ V ⊆ c.chart.target ∧ HasJointWideScreen B c i o V ∧
      HasWideRicciRangeSlope r B hSig c K i o L C η := by
  obtain ⟨δ, hδ, hδSub⟩ := hK.exists_cthickening_subset_open c.chart.open_target hKU
  let W := Metric.cthickening δ K
  let V := Metric.thickening δ K
  have hW : IsCompact W := hK.cthickening
  have hKV : K ⊆ V := Metric.self_subset_thickening hδ K
  have hVW : V ⊆ W := Metric.thickening_subset_cthickening δ K
  let F := chartInverseMetric B c
  let Q := F '' W
  have hF := chartInverseMetric_smooth B hB hSig.isNondegenerate c
  have hQ : IsCompact Q := hW.image_of_continuousOn (hF.continuousOn.mono hδSub)
  have hInv (R : ScreenMatrix) (hR : R ∈ Q) : IsUnit R.det := by
    obtain ⟨x, hx, rfl⟩ := hR
    exact chartInverseMetric_isUnit B hSig.isNondegenerate c (hδSub hx)
  have hFrame (R : ScreenMatrix) (hR : R ∈ Q) : Nonempty (LorentzFrame R) := by
    obtain ⟨x, hx, rfl⟩ := hR
    exact chartInverseMetric_has_frame B hSig c (hδSub hx)
  obtain ⟨i, o, hi, hio, hSmooth⟩ :=
    @exists_globalAngularScreenSymbol_contDiffOn (E × E) _ _ Q hQ hInv hFrame
  have hJoint : HasJointWideScreen B c i o V := by
    intro H a b
    let U := V ×ˢ ({0}ᶜ : Set E)
    have hBase : ContDiffOn ℝ ∞ (fun p : E × E => F p.1) U :=
      hF.comp contDiff_fst.contDiffOn (fun _ hp => hδSub (hVW hp.1))
    exact hSmooth U (fun p => F p.1) (fun _ => H) (fun p j => p.2 j)
      (fun _ hp => mem_image_of_mem _ (hVW hp.1))
      (fun a b => contDiffOn_pi.mp (contDiffOn_pi.mp hBase a) b)
      (fun _ _ => contDiffOn_const)
      (fun j => ((EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp contDiff_snd).contDiffOn)
      (fun p hp hz => hp.2 (by ext j; exact congrFun hz j)) a b
  obtain ⟨i₀, o₀, _, C, hi₀, hio₀, _, hC, hOld⟩ :=
    exists_actualFrozenScreen_phase_errors (r := r) B hB hSig c K hK hConv hKU
  obtain ⟨L, hL, hPhase⟩ :=
    exists_actualNull_frozenPhaseAndThinCone (r := r) B hB hSig.isSymmetric hSig.isNondegenerate c K hK hConv hKU
  refine ⟨i, o, L, C, min i i₀, V, hi, hio, hL, hC, lt_min hi hi₀,
    Metric.isOpen_thickening, hKV, hVW.trans hδSub, hJoint, ?_⟩
  intro x₀ hx₀ p hp hx hNull d hd hd₁ hSmall k hSym hRic m q ξ J S
  have hPhi : |normalizedFrozenPhase m ξ| ≤ min i i₀ :=
    (hPhase x₀ hx₀ p hp hx hNull d hd).1.trans hSmall
  rw [normalizedFrozenPhase_eq_unitPhase] at hPhi
  have hΦ : |symbolNorm m (screenUnitCovector q)| ≤ min i i₀ := hPhi
  have hNew := hΦ.trans (min_le_left _ _)
  have hOldBound := hΦ.trans (min_le_right _ _)
  have hEq : S = complexWideScreen i₀ o₀ m J q := by
    change complexWideScreen i o m J q = _
    unfold complexWideScreen
    rw [globalAngularScreenSymbol_eq_on_inner i o hi.le hio m (tensorRe J) q hNew,
      globalAngularScreenSymbol_eq_on_inner i o hi.le hio m (tensorIm J) q hNew,
      globalAngularScreenSymbol_eq_on_inner i₀ o₀ hi₀.le hio₀ m (tensorRe J) q hOldBound,
      globalAngularScreenSymbol_eq_on_inner i₀ o₀ hi₀.le hio₀ m (tensorIm J) q hOldBound]
  rw [hEq]
  have h := hOld x₀ hx₀ p hp hx hNull d hd hd₁ k hSym hRic
  exact ⟨h.1, h.2.1⟩

end Burnett.C02
