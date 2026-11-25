import Burnett.Analysis.AllScaleTransfer.RadianLowEndpointTrace
import Burnett.Analysis.AllScaleTransfer.ActualIntegerRadialPartition

set_option autoImplicit false
set_option maxHeartbeats 4500000
noncomputable section

namespace Burnett.A05

open Set Metric Filter MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier (radianTrilinearForm radianTrilinearWeight
  integrable_radianTrilinearWeight_of_bounded)
open Burnett.Analysis.LowRatio (Angles Point Window endpoint)
open scoped ContDiff ENNReal Topology

private theorem trace_weight_integrable {U : Set Angles} {a b r R A : ℝ}
    (ha : a < 0) (hb : 0 < b) (hrR : r ≤ R) (hA0 : 0 ≤ A)
    (hChart : closedBall (0 : EndpointAngle) R ×ˢ closedBall (0 : EndpointAngle) R ⊆ U)
    (M : Point → ℂ) (hM : ContinuousOn M (Window U a b))
    (hA : ∀ z ∈ Window U a b, ‖M z‖ ≤ A) (f g w : SchwartzMap E ℂ)
    (htest : ∀ᵐ p : Joint ∂(volume : Measure Joint), radianWeight (fun _ => 1) f g w p ≠ 0 →
      ‖endpointTail (endpointDirection p.1)‖ ≤ r ∧ ‖endpointTail (endpointDirection p.2)‖ ≤ r) :
    Integrable (fun p : Joint => lowEndpointM0Symbol M p * radianWeight (fun _ => 1) f g w p) := by
  classical
  let S : Set Angles := closedBall (0 : EndpointAngle) r ×ˢ closedBall (0 : EndpointAngle) r
  let θ (p : Joint) : Angles := (endpointTail (endpointDirection p.1),endpointTail (endpointDirection p.2))
  let c := S.piecewise (endpoint M) (fun _ => 0)
  have mp : MapsTo (fun z : Angles => (z,(0:ℝ))) S (Window U a b) := by
    intro z hz
    refine ⟨hChart ⟨closedBall_subset_closedBall hrR hz.1, closedBall_subset_closedBall hrR hz.2⟩, ha,hb⟩
  have con : ContinuousOn (endpoint M) S := hM.comp (by fun_prop) mp
  have mc : Measurable c := con.measurable_piecewise continuousOn_const
    (measurableSet_closedBall.prod measurableSet_closedBall)
  have dh : Measurable endpointDirection := by unfold endpointDirection; fun_prop
  have mθ : Measurable θ :=
    (endpointTail.continuous.measurable.comp (dh.comp measurable_fst)).prodMk
      (endpointTail.continuous.measurable.comp (dh.comp measurable_snd))
  have hK : Integrable (radianWeight (fun _ => (1:ℝ)) f g w : Joint → ℂ) := by
    have same : radianTrilinearWeight (fun _ => (1:ℂ)) f g w = radianWeight (fun _ => 1) f g w := by
      funext p
      change (1:ℂ) * radianWeight (fun _ => 1) f g w p = _
      exact one_mul _
    rw [← same]
    exact integrable_radianTrilinearWeight_of_bounded (fun _ => (1:ℂ))
      aestronglyMeasurable_const 1 (fun _ => norm_one.le) f g w
  refine (hK.bdd_mul' (c := A) (mc.comp mθ).aestronglyMeasurable ?_).congr ?_
  · filter_upwards with p
    change ‖c (θ p)‖ ≤ A
    by_cases hs : θ p ∈ S
    · rw [show c (θ p) = endpoint M (θ p) from piecewise_eq_of_mem S _ _ hs]
      exact hA _ (mp hs)
    · rw [show c (θ p) = 0 from piecewise_eq_of_notMem S _ _ hs,norm_zero]
      exact hA0
  · filter_upwards [htest] with p hp
    by_cases hk : radianWeight (fun _ => 1) f g w p = 0
    · simp only [hk,mul_zero]
    · have my : θ p ∈ S := ⟨mem_closedBall_zero_iff.mpr (hp hk).1,
        mem_closedBall_zero_iff.mpr (hp hk).2⟩
      simp only [Function.comp_apply,
        show c (θ p) = endpoint M (θ p) from piecewise_eq_of_mem S _ _ my]
      rfl

/-- The bounded-overlap integer scale sum represents the actual M₀ Fourier
integral and has the same constant as the finite low-endpoint estimate. -/
theorem exists_radian_lowEndpoint_M0_full_bound {U : Set Angles} (hU : IsOpen U)
    {a b r R P : ℝ} (ha : a < 0) (hb : 0 < b) (hr : 0 < r) (hR : r < R) (hP : 2 < P)
    (hChart : closedBall (0 : EndpointAngle) R ×ˢ closedBall (0 : EndpointAngle) R ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (M : Point → ℂ) (A : ℝ), 0 ≤ A → ContDiffOn ℝ 100 M (Window U a b) →
      (∀ j ≤ 100, ∀ z ∈ Window U a b, ‖iteratedFDeriv ℝ j M z‖ ≤ A) →
      ∀ (gap : ℕ) (f g w : SchwartzMap E ℂ),
        (∀ᵐ p : Joint ∂(volume : Measure Joint), radianWeight (fun _ => 1) f g w p ≠ 0 →
          ‖endpointTail (endpointDirection p.1)‖ ≤ r ∧ ‖endpointTail (endpointDirection p.2)‖ ≤ r) →
        let W := lowEndpointRadianWindows gap
        let T (j : ℤ) := radianTrilinearForm (fun p => lowEndpointM0Symbol M p * W j p) f g w
        let Z := radianTrilinearForm (fun p => lowEndpointM0Symbol M p * ∑' j, W j p) f g w
        HasSum T Z ∧ ‖Z‖ ≤ C * A * ‖f.toLp (ENNReal.ofReal 3) volume‖ *
          ‖g.toLp (ENNReal.ofReal 3) volume‖ * ‖w.toLp (ENNReal.ofReal 3) volume‖ := by
  classical
  obtain ⟨C,hC,H⟩ := exists_radian_lowEndpoint_M0_bound hU ha hb hr hR hP hChart
  refine ⟨C,hC,?_⟩
  intro M A hA hM jets gap f g w htest W T Z
  let N (p : Joint) := lowEndpointM0Symbol M p * radianWeight (fun _ => 1) f g w p
  have hN : Integrable N := trace_weight_integrable ha hb hR.le hA hChart M hM.continuousOn
    (fun z hz => by simpa only [norm_iteratedFDeriv_zero] using jets 0 (by omega) z hz) f g w htest
  let B := SchwartzMap.seminorm ℝ 0 0 endpointLowProfile * SchwartzMap.seminorm ℝ 0 0 endpointHighProfile *
    SchwartzMap.seminorm ℝ 0 0 endpointThickProfile
  have hB : 0 ≤ B := by unfold B; positivity
  have hCont (j : ℤ) : Continuous (W j) := by
    change Continuous (fun p : Joint => lowEndpointRadianWindows gap j p)
    simp only [lowEndpointRadianWindows_eq_profiles]
    fun_prop
  have hnorm (j : ℤ) (p : Joint) : ‖W j p‖ ≤ B := by
    change ‖lowEndpointRadianWindows gap j p‖ ≤ B
    rw [lowEndpointRadianWindows_eq_profiles,norm_mul,norm_mul]
    exact mul_le_mul
      (mul_le_mul (endpointLowProfile.norm_le_seminorm ℝ _) (endpointHighProfile.norm_le_seminorm ℝ _)
        (norm_nonneg _) (apply_nonneg _ _))
      (endpointThickProfile.norm_le_seminorm ℝ _) (norm_nonneg _) (by positivity)
  have hLoc (p : Joint) : ∃ I : Finset ℤ, I.card ≤ 3 ∧ ∀ j ∉ I, W j p = 0 := by
    obtain ⟨I,hI,hZero⟩ := exists_integerRadialWindow_support_card_le_three p.2
    refine ⟨I,hI,fun j hj => ?_⟩
    have hz : Burnett.Analysis.CapFourier.radialAnnularCutoff ((2 : ℝ)^j) p.2 = 0 := hZero j hj
    simp only [W,lowEndpointRadianWindows,hz,Complex.ofReal_zero,mul_zero,zero_mul]
  have hPartial (J : Finset ℤ) (p : Joint) : ‖∑ j ∈ J, W j p‖ ≤ 3 * B := by
    obtain ⟨I,hI,hZero⟩ := hLoc p
    have hEq : (∑ j ∈ J, W j p) = ∑ j ∈ J ∩ I, W j p := by
      refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
      exact fun j hj hn => hZero j (fun hi => hn (Finset.mem_inter.mpr ⟨hj,hi⟩))
    rw [hEq]
    have hCard : (J ∩ I).card ≤ 3 := (Finset.card_le_card Finset.inter_subset_right).trans hI
    calc
      _ ≤ ∑ j ∈ J ∩ I, B := norm_sum_le_of_le _ (fun j _ => hnorm j p)
      _ = ((J ∩ I).card : ℝ) * B := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hCard) hB
  let L (p : Joint) := ∑' j, W j p
  have hDCT : Tendsto (fun J : Finset ℤ => ∫ p, (∑ j ∈ J, W j p) * N p) atTop
      (𝓝 (∫ p, L p * N p)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun p => (3 * B) * ‖N p‖)
    · exact Eventually.of_forall (fun J =>
        (J.aestronglyMeasurable_fun_sum (fun j _ => (hCont j).aestronglyMeasurable)).mul hN.1)
    · exact Eventually.of_forall (fun J => Eventually.of_forall (fun p => by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hPartial J p) (norm_nonneg _)))
    · exact hN.norm.const_mul _
    · apply Eventually.of_forall
      intro p
      obtain ⟨I,_,hZero⟩ := hLoc p
      have hs : HasSum (fun j => W j p) (L p) := (summable_of_ne_finset_zero hZero).hasSum
      exact (show Tendsto (fun J : Finset ℤ => ∑ j ∈ J, W j p) atTop (𝓝 (L p)) from hs).mul
        tendsto_const_nhds
  have hForm (V : Joint → ℂ) : radianTrilinearForm (fun p => lowEndpointM0Symbol M p * V p) f g w =
      (tau^8)⁻¹ • ∫ p, V p * N p := by
    unfold radianTrilinearForm
    congr 1
    apply integral_congr_ae
    filter_upwards with p
    change (lowEndpointM0Symbol M p * V p) * radianWeight (fun _ => 1) f g w p = _
    unfold N
    ring
  have hInt (j : ℤ) : Integrable (fun p => W j p * N p) :=
    hN.bdd_mul' (c := B) (hCont j).aestronglyMeasurable (Eventually.of_forall (hnorm j))
  have hSumEq (J : Finset ℤ) : (∑ j ∈ J, T j) =
      radianTrilinearForm (fun p => lowEndpointM0Symbol M p * ∑ j ∈ J, W j p) f g w := by
    simp only [T,hForm,← Finset.smul_sum,← integral_finset_sum _ (fun j _ => hInt j),Finset.sum_mul]
  have lim : HasSum T Z := by
    change Tendsto (fun J : Finset ℤ => ∑ j ∈ J, T j) atTop (𝓝 Z)
    simp only [hSumEq,Z,hForm]
    exact hDCT.const_smul ((tau^8)⁻¹ : ℝ)
  refine ⟨lim, ?_⟩
  change Tendsto (fun J : Finset ℤ => ∑ j ∈ J, T j) atTop (𝓝 Z) at lim
  apply le_of_tendsto' (continuous_norm.continuousAt.tendsto.comp lim)
  intro J
  let n := Fintype.card (↑J : Type)
  let e : (↑J : Type) ≃ Fin n := Fintype.equivFin _
  let i : Fin n ↪ ℤ := e.symm.toEmbedding.trans ⟨Subtype.val, Subtype.val_injective⟩
  have reindex (p : Joint) : (∑ k : Fin n, W (i k) p) = ∑ j ∈ J, W j p := calc
    _ = ∑ j : (↑J : Type), W j.val p := e.symm.sum_comp (fun j => W j.val p)
    _ = _ := Finset.sum_attach J (fun j => W j p)
  simp only [Function.comp_apply,hSumEq,← reindex]
  exact H M A hA hM jets gap n i f g w htest

end Burnett.A05
