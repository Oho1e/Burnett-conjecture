import Burnett.Geometry.Cotangent.MaximalCanonicalFlowSmoothness

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option maxRecDepth 3800

noncomputable section

namespace Burnett.Geometry.CotangentHamiltonInitialFamily

open Set Filter Bundle
open scoped ContDiff Topology Manifold
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.UnitNullAngular
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.CotangentCauchyCrossing
open Burnett.Geometry.CotangentHamiltonLocalFlow Burnett.Geometry.CotangentHamiltonMaximalCurve
open Burnett.Geometry.CotangentHamiltonCauchySlice
open Burnett.Geometry.CotangentCrossingTransversality
open Burnett.Geometry.CotangentHamiltonCrossingEnergy Burnett.Geometry.CotangentHamiltonSmoothCrossing

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M]

/-- The actual Cauchy crossing energy on the punctured null cone has a local
smooth representative on the full ambient cotangent bundle at every null phase. -/
theorem exists_smooth_actualCrossingEnergy_germ (r : Metric (M := M)) (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (hL : HasLorentzSignature g) (S : Set M) (hC : RegularCauchySliceProperty g S)
    (hS : SmoothSpacelikeSlice g S) (p : CotangentBundle M) (hp : p ∈ puncturedCotangent)
    (hnull : dualEnergy g hn p = 0) :
    ∃ E : CotangentBundle M → ℝ, ContMDiffAt CotangentModelWithCorners 𝓘(ℝ) ∞ E p ∧
      ∀ᶠ q in 𝓝 p, ∀ (hq : q ∈ puncturedCotangent) (hqnull : dualEnergy g hn q = 0),
        E q = globalCrossingEnergy r g hg hn hs hL S hC ⟨q, hq, hqnull⟩ := by
  let A := maximalPuncturedTrajectory g hg hn hs p hp
  have hmax (B : CanonicalTrajectory g p) : B.domain ⊆ A.domain :=
    (maximalPuncturedTrajectory_spec g hg hn hs p hp B).1
  have hUnique := maximal_null_orbit_unique_cauchy_crossing g hg hn hs hL A hp hnull hmax S hC
  let t₀ := crossingTime S A.domain A.curve hUnique
  have ht : t₀ ∈ A.domain ∧ (A.curve t₀).1 ∈ S := crossingTime_spec S A.domain A.curve hUnique
  let F := maximalPuncturedFlow g hg hn hs
  let D := maximalPuncturedFlowDomain g hg hn hs
  have hpD : (p, t₀) ∈ D := ⟨hp, ht.1⟩
  have hF₀ : F (p, t₀) = A.curve t₀ := maximalPuncturedFlow_eq_curve g hg hn hs p hp t₀
  obtain ⟨hD, hF⟩ := maximalPuncturedFlow_jointSmooth g hg hn hs
  have hFAt := hF.contMDiffAt (hD.mem_nhds hpD)
  obtain ⟨f, hf⟩ := hS (A.curve t₀).1 ht.2
  obtain ⟨U, hU, hqU, hfU, hLevel⟩ := hf.localModel
  have hfAt : ContMDiffAt Model 𝓘(ℝ) ∞ f (F (p, t₀)).1 := by
    rw [hF₀]
    exact hfU.contMDiffAt (hU.mem_nhds hqU)
  let c := p.proj
  let x₀ := cotangentChart c p
  let χ := cotangentChartInverse c
  have hpC : p ∈ cotangentSource c := mem_chart_source CoordinateSpace p.proj
  have hxC : x₀ ∈ phaseTarget c := (cotangentChart_mem_punctured c p hpC hp).1
  have hχ₀ : χ x₀ = p := cotangentChart_left_inv c hpC
  have hχ : ContMDiffAt 𝓘(ℝ, Phase) CotangentModelWithCorners ∞ χ x₀ := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (contMDiffOn_cotangentChartInverse c).contMDiffAt ((isOpen_phaseTarget c).mem_nhds hxC)
  let K (z : Phase × ℝ) : CotangentBundle M × ℝ := (χ z.1, z.2)
  have hK₀ : K (x₀, t₀) = (p, t₀) := Prod.ext hχ₀ rfl
  have hK : ContMDiffAt 𝓘(ℝ, Phase × ℝ) (CotangentModelWithCorners.prod 𝓘(ℝ)) ∞ K (x₀, t₀) :=
    (hχ.comp (x₀, t₀) contDiff_fst.contDiffAt.contMDiffAt).prodMk contDiff_snd.contDiffAt.contMDiffAt
  have hProjection : ContMDiff CotangentModelWithCorners Model ∞ (fun q : CotangentBundle M => q.1) :=
    contMDiff_proj (𝕜 := ℝ) (IB := Model) (n := ∞) (CotangentFiber (M := M))
  let Z (z : Phase × ℝ) := f (F (K z)).1
  have hZ : ContDiffAt ℝ ∞ Z (x₀, t₀) := by
    have hBase : ContMDiffAt 𝓘(ℝ, Phase × ℝ) Model ∞ (fun z => (F (K z)).1) (x₀, t₀) :=
      hProjection.contMDiffAt.comp (x₀, t₀) (hFAt.comp_of_eq hK hK₀)
    have hBase₀ : (F (K (x₀, t₀))).1 = (F (p, t₀)).1 := congrArg (fun z => (F z).1) hK₀
    exact (hfAt.comp_of_eq hBase hBase₀).contDiffAt
  have hZ₀ : Z (x₀, t₀) = 0 := by
    change f (F (K (x₀, t₀))).1 = 0
    rw [hK₀, hF₀]
    exact (hLevel _ hqU).mp ht.2
  let d := mfderiv Model 𝓘(ℝ) f (A.curve t₀).1 (canonicalBaseVelocity g (A.curve t₀))
  obtain ⟨_, hderiv, hd, _⟩ := canonicalTrajectory_spacelike_hit_transverse g hg hn hs A hp hnull
    S t₀ ht.1 ht.2 f hf
  have hZtime : HasDerivAt (fun t => Z (x₀, t)) d t₀ := by
    have hEval (t : ℝ) : Z (x₀, t) = f (A.curve t).1 := by
      change f (F (χ x₀, t)).1 = _
      have hFt : F (p, t) = A.curve t := maximalPuncturedFlow_eq_curve g hg hn hs p hp t
      rw [hχ₀, hFt]
    simpa only [hEval] using hderiv
  obtain ⟨τ, hτ₀, hτ, hτz⟩ := exists_smooth_time_of_transverse_zero Z x₀ t₀ d hZ hZ₀ hZtime hd
  have hChart : ContMDiffAt CotangentModelWithCorners 𝓘(ℝ, Phase) ∞ (cotangentChart c) p := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact (contMDiffOn_cotangentChart c).contMDiffAt ((isOpen_cotangentSource c).mem_nhds hpC)
  let T (q : CotangentBundle M) := (q, τ (cotangentChart c q))
  have hT₀ : T p = (p, t₀) := Prod.ext rfl hτ₀
  have hT : ContMDiffAt CotangentModelWithCorners (CotangentModelWithCorners.prod 𝓘(ℝ)) ∞ T p :=
    contMDiffAt_id.prodMk (hτ.contMDiffAt.comp p hChart)
  let H (q : CotangentBundle M) := F (T q)
  have hH : ContMDiffAt CotangentModelWithCorners CotangentModelWithCorners ∞ H p :=
    hFAt.comp_of_eq hT hT₀
  have hH₀ : H p = A.curve t₀ := (congrArg F hT₀).trans hF₀
  have htd : ∀ᶠ q in 𝓝 p, T q ∈ D :=
    hT.continuousAt.preimage_mem_nhds (hD.mem_nhds (hT₀.symm ▸ hpD))
  have hHU : (H p).1 ∈ U := by rw [hH₀]; exact hqU
  have hu : ∀ᶠ q in 𝓝 p, (H q).1 ∈ U :=
    (hProjection.contMDiffAt.comp p hH).continuousAt.preimage_mem_nhds
      (hU.mem_nhds hHU)
  have hqz : ∀ᶠ q in 𝓝 p, Z (cotangentChart c q, τ (cotangentChart c q)) = 0 :=
    hChart.continuousAt.eventually hτz
  have hPunct := CanonicalTrajectory.punctured g hg hn hs A hp ht.1
  refine ⟨cotangentNorm r ∘ H, (cotangentNorm_contMDiffAt_punctured r _ hPunct).comp_of_eq hH hH₀, ?_⟩
  filter_upwards [htd, hu, hqz, (isOpen_cotangentSource c).mem_nhds hpC] with q hdq huq hzq hcq
  intro hq hqnull
  let B := maximalPuncturedTrajectory g hg hn hs q hq
  let t := τ (cotangentChart c q)
  obtain ⟨_, htB⟩ := hdq
  have hB : H q = B.curve t := maximalPuncturedFlow_eq_curve g hg hn hs q hq t
  have hzero : f (H q).1 = 0 := by
    change f (F (χ (cotangentChart c q), t)).1 = 0 at hzq
    have hLeft : χ (cotangentChart c q) = q := cotangentChart_left_inv c hcq
    rw [hLeft] at hzq
    exact hzq
  have hHit : (B.curve t).1 ∈ S := hB ▸ (hLevel _ huq).mpr hzero
  have hEq := globalCrossingPoint_eq_of_orbit_hit g hg hn hs hL S hC ⟨q, hq, hqnull⟩ B htB hHit
  exact congrArg (cotangentNorm r) (hB.trans hEq.symm)

end Burnett.Geometry.CotangentHamiltonInitialFamily
