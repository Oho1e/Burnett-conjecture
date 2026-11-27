import Burnett.Analysis.AllScaleTransfer.AnalyticNearData

set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 5500

noncomputable section

namespace Burnett.A05

open Filter Metric Set
open Burnett.Analysis.CapFourier Burnett.C02 Burnett.A02.FrequencySplit
open Burnett.Analysis.LowRatio (Point)
open scoped ContDiff Topology

open private moveAxis signedDirection_margin from Burnett.Analysis.AllScaleTransfer.SphereAtlas

private theorem wardSphere_endpointDirection (s : WardSphereChart) {p : E}
    (hp : p ∈ wardSphereChartAnnulus s) :
    endpointDirection p ∈ wardSphereChartAnnulus s ∧
      wardSphereChartAngle s (endpointDirection p) = wardSphereChartAngle s p := by
  have hn : 0 < ‖p‖ := (by norm_num : (0 : ℝ) < 1/4).trans hp.1
  have hunit := mem_sphere_zero_iff_norm.mp (endpointDirection_mem_sphere (norm_pos_iff.mp hn))
  have hmove : moveAxis s.1 (endpointDirection p) = endpointDirection (moveAxis s.1 p) := by
    simp only [endpointDirection, map_smul, LinearIsometryEquiv.norm_map]
  refine ⟨⟨by rw [hunit]; norm_num, by rw [hunit]; norm_num, ?_⟩, ?_⟩
  · rw [hunit, mul_one, hmove]
    exact signedDirection_margin s p hp
  · simp only [wardSphereChartAngle, endpointDirection, map_smul, LinearIsometryEquiv.norm_map,
      norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg p)), inv_mul_cancel₀ hn.ne',
      inv_one, one_smul]

/-- The positive-ratio formulas of a single signed multiplier determine
one bounded Borel zero-ratio trace on the two normalized frequency directions. -/
theorem exists_wardPair_zeroRatioTrace_of_positiveAgreement
    (b A : ℝ) (hb : 0 < b) (hA : 0 ≤ A)
    (F : Joint → ℂ) (M : WardPairChart → Point → ℂ)
    (smooth : ∀ i, ContDiffOn ℝ 100 (M i) (wardPairChartDomain i ×ˢ Ico (0 : ℝ) b))
    (jets : ∀ i n, n ≤ 100 → ∀ z ∈ wardPairChartDomain i ×ˢ Ico (0 : ℝ) b,
      ‖iteratedFDerivWithin ℝ n (M i) (wardPairChartDomain i ×ˢ Ico (0 : ℝ) b) z‖ ≤ A)
    (positive : ∀ i pq, pq ∈ wardPairChartAnnulus i → ∀ t : ℝ, 0 < t →
      let ρ := t*(‖pq.1‖/‖pq.2‖)
      ρ ∈ Ioo (0 : ℝ) b → F (t • pq.1,pq.2) = M i (wardPairChartAngles i pq,ρ)) :
    ∃ M₀ : Joint → ℂ, Measurable M₀ ∧ (∀ q, ‖M₀ q‖ ≤ A) ∧
      ∀ i pq, pq ∈ wardPairChartAnnulus i →
        M₀ (endpointDirection pq.1,endpointDirection pq.2) = M i (wardPairChartAngles i pq,0) := by
  classical
  let V := wardPairChartAnnulus
  let U := ⋃ i, V i
  let z (i : WardPairChart) (p : Joint) := M i (wardPairChartAngles i p,0)
  have agree (i j : WardPairChart) (p : Joint) (hi : p ∈ V i) (hj : p ∈ V j) : z i p = z j p := by
    have hR : 0 < ‖p.1‖ / ‖p.2‖ := div_pos ((by norm_num : (0 : ℝ) < 1/4).trans hi.1.1)
      ((by norm_num : (0 : ℝ) < 1/4).trans hi.2.1)
    let G (i : WardPairChart) (t : ℝ) := M i (wardPairChartAngles i p,t)
    letI := left_nhdsWithin_Ioo_neBot hb
    have limit (k : WardPairChart) (hk : p ∈ V k) :
        Tendsto (G k) (𝓝[Ioo (0 : ℝ) b] 0) (𝓝 (z k p)) := by
      have hAngle := wardPairChartAngles_mapsTo k hk
      have h0 : (wardPairChartAngles k p,0) ∈ wardPairChartDomain k ×ˢ Ico (0 : ℝ) b :=
        ⟨hAngle,le_rfl,hb⟩
      have hLine : Continuous (fun t : ℝ => (wardPairChartAngles k p,t)) := continuous_const.prodMk continuous_id
      have h := (smooth k).continuousOn _ h0 |>.comp hLine.continuousWithinAt
        (show MapsTo (fun t : ℝ => (wardPairChartAngles k p,t)) (Ioo (0 : ℝ) b)
          (wardPairChartDomain k ×ˢ Ico (0 : ℝ) b) from fun _ ht => ⟨hAngle,ht.1.le,ht.2⟩)
      exact h
    have eq : G i =ᶠ[𝓝[Ioo (0 : ℝ) b] 0] G j := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have hτ : 0 < t / (‖p.1‖ / ‖p.2‖) := div_pos ht.1 hR
      have ht' : t / (‖p.1‖ / ‖p.2‖) * (‖p.1‖ / ‖p.2‖) = t := div_mul_cancel₀ _ hR.ne'
      have hRatio : t / (‖p.1‖ / ‖p.2‖) * (‖p.1‖ / ‖p.2‖) ∈ Ioo (0 : ℝ) b := by
        rwa [ht']
      have hti := positive i p hi _ hτ hRatio
      have htj := positive j p hj _ hτ hRatio
      simpa only [G,ht'] using hti.symm.trans htj
    exact tendsto_nhds_unique (limit i hi) ((limit j hj).congr' eq.symm)
  let H (p : Joint) := if hx : p ∈ U then z (mem_iUnion.mp hx).choose p else 0
  have eqRaw (i : WardPairChart) (p : Joint) (hp : p ∈ V i) : H p = z i p := by
    have hu : p ∈ U := mem_iUnion.mpr ⟨i,hp⟩
    change (if hx : p ∈ U then z (mem_iUnion.mp hx).choose p else 0) = z i p
    rw [dif_pos hu]
    exact agree _ i p (mem_iUnion.mp hu).choose_spec hp
  have hOpen : IsOpen U := isOpen_iUnion wardPairChartAnnulus_open
  have hCont : ContinuousOn H U := by
    intro p hp
    obtain ⟨i,hi⟩ := mem_iUnion.mp hp
    have hLocal : ContinuousOn (z i) (V i) := by
      apply (smooth i).continuousOn.comp ((wardPairChartAngles_smooth i).continuousOn.prodMk continuousOn_const)
      exact fun q hq => ⟨wardPairChartAngles_mapsTo i hq,le_rfl,hb⟩
    have eq : H =ᶠ[𝓝 p] z i := by
      filter_upwards [(wardPairChartAnnulus_open i).mem_nhds hi] with q hq
      exact eqRaw i q hq
    exact ((hLocal.continuousAt ((wardPairChartAnnulus_open i).mem_nhds hi)).congr eq.symm).continuousWithinAt
  have hPiece : U.piecewise H (fun _ => 0) = H := by
    funext p
    by_cases hp : p ∈ U
    · simp [Set.piecewise, hp]
    · simp [Set.piecewise, H, hp]
  refine ⟨H,hPiece ▸ hCont.measurable_piecewise continuousOn_const hOpen.measurableSet,?_,?_⟩
  · intro q
    by_cases hq : q ∈ U
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hq
      rw [eqRaw i q hi]
      simpa only [z, norm_iteratedFDerivWithin_zero] using
        jets i 0 (by norm_num) (wardPairChartAngles i q,0) ⟨wardPairChartAngles_mapsTo i hi,le_rfl,hb⟩
    · simp [H,hq,hA]
  · intro i q hq
    obtain ⟨h₁,e₁⟩ := wardSphere_endpointDirection i.1 hq.1
    obtain ⟨h₂,e₂⟩ := wardSphere_endpointDirection i.2 hq.2
    rw [eqRaw i _ (show (endpointDirection q.1,endpointDirection q.2) ∈ V i from ⟨h₁,h₂⟩)]
    simp only [z, wardPairChartAngles, e₁, e₂]

end Burnett.A05

#print axioms Burnett.A05.exists_wardPair_zeroRatioTrace_of_positiveAgreement
