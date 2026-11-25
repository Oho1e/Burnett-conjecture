import Burnett.Geometry.Cotangent.PuncturedCanonicalFlow

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option maxRecDepth 3700

noncomputable section

namespace Burnett.Geometry.CotangentHamiltonInitialFamily

open Set Filter
open scoped ContDiff Topology Manifold
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.CotangentHamiltonMaximalCurve

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M]

variable (g : Field (M := M)) (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g)

private def smoothFlowInterior : Set (CotangentBundle M × ℝ) := interior
  {qt | qt ∈ maximalPuncturedFlowDomain g hg hn hs ∧
    ContMDiffAt (CotangentModelWithCorners.prod 𝓘(ℝ)) CotangentModelWithCorners ∞
      (maximalPuncturedFlow g hg hn hs) qt}

private theorem smoothFlowInterior_spec {z : CotangentBundle M × ℝ}
    (hz : z ∈ smoothFlowInterior g hg hn hs) : z ∈ maximalPuncturedFlowDomain g hg hn hs ∧
    ContMDiffAt (CotangentModelWithCorners.prod 𝓘(ℝ)) CotangentModelWithCorners ∞
      (maximalPuncturedFlow g hg hn hs) z := by
  change z ∈ {qt | qt ∈ maximalPuncturedFlowDomain g hg hn hs ∧
    ContMDiffAt (CotangentModelWithCorners.prod 𝓘(ℝ)) CotangentModelWithCorners ∞
      (maximalPuncturedFlow g hg hn hs) qt}
  exact interior_subset hz

private theorem smoothFlowInterior_at_zero (q : CotangentBundle M) (hq : q ∈ puncturedCotangent) :
    (q, 0) ∈ smoothFlowInterior g hg hn hs :=
  mem_interior_iff_mem_nhds.mpr (eventually_maximalPuncturedFlow_smooth_initial g hg hn hs q hq)

/-- The canonical restart law transfers smoothness and domain membership
through one fixed intermediate time, including across overlapping charts. -/
private theorem smoothFlowInterior_restart (q : CotangentBundle M) (s t : ℝ)
    (hstart : (q, s) ∈ smoothFlowInterior g hg hn hs)
    (hnext : (maximalPuncturedFlow g hg hn hs (q, s), t - s) ∈ smoothFlowInterior g hg hn hs) :
    (q, t) ∈ smoothFlowInterior g hg hn hs := by
  let F := maximalPuncturedFlow g hg hn hs
  let L (z : CotangentBundle M × ℝ) : CotangentBundle M × ℝ := (z.1, s)
  let H (z : CotangentBundle M × ℝ) : CotangentBundle M × ℝ := (F (L z), z.2 - s)
  let U := smoothFlowInterior g hg hn hs
  have hU : IsOpen U := isOpen_interior
  have hL : ContMDiff (CotangentModelWithCorners.prod 𝓘(ℝ))
      (CotangentModelWithCorners.prod 𝓘(ℝ)) ∞ L := contMDiff_fst.prodMk contMDiff_const
  have htime : ContMDiff (CotangentModelWithCorners.prod 𝓘(ℝ)) 𝓘(ℝ) ∞
      (fun z : CotangentBundle M × ℝ => z.2 - s) :=
    ((contDiff_id.sub contDiff_const : ContDiff ℝ ∞ (fun t : ℝ => t - s)).contMDiff).comp contMDiff_snd
  have hHs {z : CotangentBundle M × ℝ} (hz : L z ∈ U) : ContMDiffAt (CotangentModelWithCorners.prod 𝓘(ℝ))
      (CotangentModelWithCorners.prod 𝓘(ℝ)) ∞ H z :=
    (((smoothFlowInterior_spec g hg hn hs hz).2).comp z hL.contMDiffAt).prodMk htime.contMDiffAt
  have hLnear : ∀ᶠ z in 𝓝 (q, t), L z ∈ U :=
    hL.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hstart)
  have hHnear : ∀ᶠ z in 𝓝 (q, t), H z ∈ U :=
    (hHs (z := (q, t)) hstart).continuousAt.preimage_mem_nhds (hU.mem_nhds hnext)
  have hEq : ∀ᶠ z in 𝓝 (q, t), z ∈ maximalPuncturedFlowDomain g hg hn hs ∧ F z = F (H z) := by
    filter_upwards [hLnear, hHnear] with z hz hw
    have h := maximalPuncturedFlow_restart g hg hn hs z.1 s (z.2 - s)
      (smoothFlowInterior_spec g hg hn hs hz).1 (smoothFlowInterior_spec g hg hn hs hw).1
    simpa only [sub_add_cancel, Prod.eta] using h
  have hEqGerm : ∀ᶠ z in 𝓝 (q, t), F =ᶠ[𝓝 z] F ∘ H :=
    eventually_eventually_nhds.mpr (hEq.mono fun _ hz => hz.2)
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hLnear, hHnear, hEq, hEqGerm] with z hz hw hdom he
  exact ⟨hdom.1, (((smoothFlowInterior_spec g hg hn hs hw).2).comp z (hHs hz)).congr_of_eventuallyEq he⟩

/-- The domain of the actual maximal punctured phase map is open, and the
map is jointly smooth in initial phase and affine time throughout it. -/
theorem maximalPuncturedFlow_jointSmooth :
    IsOpen (maximalPuncturedFlowDomain g hg hn hs) ∧
    ContMDiffOn (CotangentModelWithCorners.prod 𝓘(ℝ)) CotangentModelWithCorners ∞
      (maximalPuncturedFlow g hg hn hs) (maximalPuncturedFlowDomain g hg hn hs) := by
  let F := maximalPuncturedFlow g hg hn hs
  let U := smoothFlowInterior g hg hn hs
  have hU : IsOpen U := isOpen_interior
  have hAll : maximalPuncturedFlowDomain g hg hn hs ⊆ U := by
    intro z hz
    rcases z with ⟨q, u⟩
    obtain ⟨hq, hu⟩ := hz
    let A := maximalPuncturedTrajectory g hg hn hs q hq
    let J := A.domain
    have hFtime : (fun t => F (q, t)) = A.curve :=
      funext (maximalPuncturedFlow_eq_curve g hg hn hs q hq)
    letI : PreconnectedSpace J := isPreconnected_iff_preconnectedSpace.mp A.domain_interval.isPreconnected
    let Good : Set J := {t | (q, (t : ℝ)) ∈ U}
    have hGoodOpen : IsOpen Good :=
      hU.preimage (continuous_const.prodMk continuous_subtype_val)
    have hGoodClosed : IsClosed Good := by
      rw [← isOpen_compl_iff]
      refine isOpen_iff_mem_nhds.mpr fun t ht => ?_
      let r : ℝ := t
      have htbad : (q, r) ∉ U := ht
      have hp : F (q, r) ∈ puncturedCotangent := by
        rw [congrFun hFtime r]
        exact CanonicalTrajectory.punctured g hg hn hs A hq t.property
      have hRestart₀ : (F (q, r), 0) ∈ U := smoothFlowInterior_at_zero g hg hn hs _ hp
      have hFcont : ContinuousAt (fun s => F (q, s)) r := by
        rw [hFtime]
        exact (A.integral.continuousOn r t.property).continuousAt (A.domain_open.mem_nhds t.property)
      have hP : ContinuousAt (fun s => (F (q, s), r - s)) r :=
        hFcont.prodMk (continuous_const.sub continuous_id).continuousAt
      have hPnear : ∀ᶠ s in 𝓝 r, (F (q, s), r - s) ∈ U := by
        apply hP.preimage_mem_nhds
        simpa only [sub_self] using hU.mem_nhds hRestart₀
      have hNotGood : ∀ᶠ s in 𝓝 r, (q, s) ∉ U := by
        filter_upwards [hPnear] with s hs'
        exact fun hbefore => htbad (smoothFlowInterior_restart g hg hn hs q s r hbefore hs')
      exact continuous_subtype_val.continuousAt.eventually hNotGood
    have hAllTimes : Good = univ := (show IsClopen Good from ⟨hGoodClosed, hGoodOpen⟩).eq_univ
      ⟨⟨0, A.zero_mem⟩, smoothFlowInterior_at_zero g hg hn hs q hq⟩
    have hgu : (⟨u, hu⟩ : J) ∈ Good := hAllTimes ▸ mem_univ _
    exact hgu
  have hD : IsOpen (maximalPuncturedFlowDomain g hg hn hs) := isOpen_iff_mem_nhds.mpr fun z hz =>
    mem_of_superset (hU.mem_nhds (hAll hz)) (fun _ hp => (smoothFlowInterior_spec g hg hn hs hp).1)
  exact ⟨hD, fun z hz => (smoothFlowInterior_spec g hg hn hs (hAll hz)).2.contMDiffWithinAt⟩

end Burnett.Geometry.CotangentHamiltonInitialFamily
