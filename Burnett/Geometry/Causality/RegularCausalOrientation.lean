import Burnett.Geometry.Causality.IntrinsicCausalChartSegments
import Burnett.Geometry.Causality.ChartCausalConeMargin

set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 4000

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set Filter Bundle
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.CotangentHamiltonCauchySlice

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

private def timePair {g : Field (M := M)} (o : TimeOrientation g) (γ : ℝ → M) (t : ℝ) : ℝ :=
  g (γ t) (o.vector (γ t)) ((mfderiv 𝓘(ℝ) Model γ t) (1 : ℝ))

private theorem timePair_eq_of_hasMFDerivAt {g : Field (M := M)}
    (o : TimeOrientation g) (γ : ℝ → M) (t : ℝ) (v : TangentSpace Model (γ t))
    (hd : HasMFDerivAt 𝓘(ℝ) Model γ t ((1 : ℝ →L[ℝ] ℝ).smulRight v)) :
    timePair o γ t = g (γ t) (o.vector (γ t)) v := by
  rw [timePair, hd.mfderiv]
  change g (γ t) (o.vector (γ t)) ((1 : ℝ) • v) = g (γ t) (o.vector (γ t)) v
  rw [one_smul]

/-- The sign of the intrinsic time pairing is continuous along a continuously
differentiable regular causal path and cannot change on an interval. -/
theorem regularCausal_uniform_timeOrientation {g : Field (M := M)} (hg : IsSmooth g)
    (hL : HasLorentzSignature g) (o : TimeOrientation g) (γ : ℝ → M)
    {I : Set ℝ} (hI : IsOpen I) (hOrd : I.OrdConnected) (hNe : I.Nonempty)
    (hγ : ContMDiffOn 𝓘(ℝ) Model 1 γ I) (hReg : RegularCausalOn g γ I) :
    RegularFutureOn o γ I ∨ RegularFutureOn o.reverse γ I := by
  have hPairNe (t : ℝ) (ht : t ∈ I) : timePair o γ t ≠ 0 := by
    obtain ⟨v, hv, hne, hcaus⟩ := hReg t ht
    rw [timePair_eq_of_hasMFDerivAt o γ t v hv]
    let x := γ t
    let B : LinearMap.BilinForm ℝ (TangentSpace Model x) := LinearMap.mk₂ ℝ
      (fun u z => g x u z) (by intros; simp [map_add]) (by intros; simp [map_smul])
      (by intros; simp [map_add]) (by intros; simp [map_smul])
    obtain ⟨b, hb⟩ := hL x
    intro hz
    exact (not_lt_of_ge hcaus) (positive_of_timelike_orthogonal B b hb (o.timelike x) hne hz)
  have hPair : ContinuousOn (timePair o γ) I := by
    intro s hs
    let c := γ s
    let e := chartAt E c
    let y := e ∘ γ
    let T := ChartVectorField.coordinateVector o.vector c
    have hc : c ∈ e.source := mem_chart_source E c
    have hgc : ContinuousOn γ I := hγ.continuousOn
    let J := I ∩ γ ⁻¹' e.source
    have hJ : IsOpen J := hgc.isOpen_inter_preimage hI e.open_source
    have hsJ : s ∈ J := ⟨hs, hc⟩
    have hE (t : ℝ) (ht : t ∈ J) : γ t ∈ e.source := ht.2
    have hChart : ContMDiffOn Model Model 1 e e.source := contMDiffOn_chart
    have hyJ : ContDiffOn ℝ 1 y J := (hChart.comp (hγ.mono inter_subset_left) hE).contDiffOn
    have hyS : ContinuousAt y s := hyJ.continuousOn.continuousAt (hJ.mem_nhds hsJ)
    have hyT : y s ∈ e.target := e.mapsTo hc
    have hTS : ContinuousAt (T ∘ y) s :=
      ((ChartVectorField.contDiffOn_coordinateVector o.vector o.smooth c).continuousOn.continuousAt
        (e.open_target.mem_nhds hyT)).comp hyS
    have hdS : ContinuousAt (deriv y) s :=
      (hyJ.continuousOn_deriv_of_isOpen hJ (by norm_num)).continuousAt (hJ.mem_nhds hsJ)
    have hCont := continuousAt_actual_chart_pairing g hg c s y (T ∘ y) (deriv y) hyS hTS hdS hyT
    have hEq : (fun t => coordinateBilinear g c (y t) ((T ∘ y) t) (deriv y t)) =ᶠ[𝓝 s] timePair o γ := by
      filter_upwards [hJ.mem_nhds hsJ] with t ht
      obtain ⟨v, hv, _, _⟩ := hReg t ht.1
      obtain ⟨_, hFrame⟩ := chart_deriv_of_intrinsic_velocity γ c t (hE t ht) v hv
      have htT : y t ∈ e.target := e.mapsTo (hE t ht)
      change g (e.symm (y t)) (tangentFrame c (e.symm (y t)) (T (y t)))
        (tangentFrame c (e.symm (y t)) (deriv y t)) = timePair o γ t
      rw [ChartVectorField.tangentFrame_coordinateVector o.vector c htT]
      change g (e.symm (y t)) (o.vector (e.symm (y t))) (tangentFrame c (e.symm (y t)) (deriv y t)) =
        timePair o γ t
      have hInv : e.symm (y t) = γ t := e.left_inv (hE t ht)
      rw [hInv, hFrame, timePair_eq_of_hasMFDerivAt o γ t v hv]
    exact (hCont.congr hEq).continuousWithinAt
  have hConnected : IsPreconnected I := isPreconnected_iff_ordConnected.mpr hOrd
  obtain ⟨a, ha⟩ := hNe
  rcases lt_or_gt_of_ne (hPairNe a ha) with hneg | hpos
  · left
    intro t ht
    obtain ⟨v, hv, hne, hcaus⟩ := hReg t ht
    refine ⟨v, hv, hne, hcaus, ?_⟩
    rw [← timePair_eq_of_hasMFDerivAt o γ t v hv]
    by_contra! hOpp
    obtain ⟨s, hs, hz⟩ := hConnected.intermediate_value ha ht hPair ⟨hneg.le, hOpp⟩
    exact hPairNe s hs hz
  · right
    intro t ht
    obtain ⟨v, hv, hne, hcaus⟩ := hReg t ht
    refine ⟨v, hv, hne, hcaus, ?_⟩
    have hGt : 0 < timePair o γ t := by
      by_contra! hOpp
      obtain ⟨s, hs, hz⟩ := hConnected.intermediate_value ht ha hPair ⟨hOpp, hpos.le⟩
      exact hPairNe s hs hz
    rw [timePair_eq_of_hasMFDerivAt o γ t v hv] at hGt
    change g (γ t) (-o.vector (γ t)) v < 0
    simpa only [map_neg, ContinuousLinearMap.neg_apply] using neg_neg_of_pos hGt

/-- Reversing the affine parameter of a past-oriented regular causal path gives
a future-oriented regular causal path for the original time orientation. -/
theorem regularFuture_reverse_parameter {g : Field (M := M)} (o : TimeOrientation g)
    (γ : ℝ → M) {I : Set ℝ} (h : RegularFutureOn o.reverse γ I) :
    RegularFutureOn o (fun t => γ (-t)) (-I) := by
  intro t ht
  obtain ⟨v, hD, hn, hC, hT⟩ := h (-t) (Set.mem_neg.mp ht)
  have hNeg : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ) (fun t : ℝ => -t) t (-(1 : ℝ →L[ℝ] ℝ)) :=
    ((hasFDerivAt_id t).neg).hasMFDerivAt
  have hComp := hD.comp t hNeg
  refine ⟨-v, ?_, neg_ne_zero.mpr hn, ?_, ?_⟩
  · apply hComp.congr_mfderiv
    apply ContinuousLinearMap.ext
    intro a
    change ℝ at a
    change (-a) • v = a • (-v)
    rw [neg_smul, smul_neg]
  · simpa only [map_neg, ContinuousLinearMap.neg_apply, neg_neg] using hC
  · change g (γ (-t)) (-o.vector (γ (-t))) v < 0 at hT
    simpa only [map_neg, ContinuousLinearMap.neg_apply] using hT

/-- The genuine causal relation orders the entire regular path, with the
direction of the order determined once for the connected affine interval. -/
theorem chartCausalRelation_orders_regular_curve {g : Field (M := M)} (hg : IsSmooth g)
    (hL : HasLorentzSignature g) (o : TimeOrientation g) (γ : ℝ → M)
    {I : Set ℝ} (hI : IsOpen I) (hOrd : I.OrdConnected) (hNe : I.Nonempty)
    (hγ : ContMDiffOn 𝓘(ℝ) Model 1 γ I) (hReg : RegularCausalOn g γ I) :
    (∀ ⦃a b : ℝ⦄, a ∈ I → b ∈ I → a ≤ b → (γ a, γ b) ∈ chartCausalRelation o) ∨
    (∀ ⦃a b : ℝ⦄, a ∈ I → b ∈ I → a ≤ b → (γ b, γ a) ∈ chartCausalRelation o) := by
  rcases regularCausal_uniform_timeOrientation hg hL o γ hI hOrd hNe hγ hReg with hF | hP
  · left
    intro a b ha hb hab
    rcases hab.lt_or_eq with hab | rfl
    · exact chartCausalRelation_of_regular_future_curve hg hL o γ hI hγ hF hab (hOrd.out ha hb)
    · exact Relation.ReflTransGen.refl
  · right
    intro a b ha hb hab
    rcases hab.lt_or_eq with hab | rfl
    · let β : ℝ → M := fun t => γ (-t)
      have hOpen : IsOpen (-I) := by
        change IsOpen ((fun t : ℝ => -t) ⁻¹' I)
        exact hI.preimage continuous_neg
      have hNeg : ContMDiff 𝓘(ℝ) 𝓘(ℝ) 1 (fun t : ℝ => -t) := contDiff_neg.contMDiff
      have hβ : ContMDiffOn 𝓘(ℝ) Model 1 β (-I) :=
        hγ.comp hNeg.contMDiffOn (fun _ ht => Set.mem_neg.mp ht)
      have hSeg : Icc (-b) (-a) ⊆ -I := fun t ht =>
        Set.mem_neg.mpr (hOrd.out ha hb ⟨by linarith [ht.2], by linarith [ht.1]⟩)
      have hR := chartCausalRelation_of_regular_future_curve hg hL o β hOpen hβ
        (regularFuture_reverse_parameter o γ hP) (neg_lt_neg hab) hSeg
      simpa only [β, neg_neg] using hR
    · exact Relation.ReflTransGen.refl

end Burnett.Geometry.FiniteCausalVolume
